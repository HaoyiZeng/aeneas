import AeneasIris.Tactics.Core
import AeneasIris.AtomicWpi
import Iris.BI.Lib.Atomic

/-! # The `Arc` interface -/

namespace AeneasIris

open Iris BI Aeneas.Data.Coinductive
open AeneasIris.AtomicWpi
open Aeneas.Std (Loc)

/-! ## The carriers

An `Arc<T>` is a pointer to a control block; these say what that pointer is, and
nothing about the protocol on the counts.  They are declared here rather than in
an implementation because they are what a client's *types* are built from -- and
because a client type that recurses through one, as `Capability` does, needs an
inductive head at the recursive occurrence.  The kernel's positivity check is
syntactic: neither an `abbrev` alias nor a field of `ArcAPI` would do.

`T` is phantom in both: a handle is three locations, whatever it points at.  It
is kept as an index anyway, so that a handle to one thing cannot be passed where
a handle to another is expected. -/

/-- Model of `my_std::Arc<T>`. -/
structure Arc (T : Type) where
  strong : Loc
  weak : Loc
  data : Loc
deriving DecidableEq, Repr

/-- Model of `my_std::Weak<T>`. -/
inductive Weak (T : Type)
  | dangling
  | live (a : Arc T)
deriving DecidableEq

section Interface

variable {hlc : Iris.HasLC}

/-- A reference-counted pointer to `T`, as a menu of operations, four abstract
predicates, and the laws relating them.

Generic in the effect row `E`, the handler `Hd` and the `Mode`, so a client
programs against the interface at whatever language it is itself written in.

The carriers are not fields: `Arc` and `Weak` are declared above, and every
implementation uses those.  What an implementation is free to choose is the
protocol -- the ghost state, the counting discipline, whether the counts are
atomic -- not the shape of the pointer.  The class still fixes one `T`, unlike
`RwLockAPI`, because the ghost state stores the payload
(`ArcMeta T = LeibnizO (Arc T × T)`) and so `ArcG GF T` is per-`T`; a single
`GF` cannot supply it for every `T`.

The shared resource is `arcAuth γ n k` -- the control block and the two counts --
and every operation that moves a count is stated as an atomic triple against it.
`deref` is the exception: `isArc` carries a share of the payload, so reading it
needs nothing shared, which is the whole point of an `Arc`.

Weak references come in two kinds, and which spec applies is decided by the
*resource* a client holds, `isWeak γ w v` or `isDanglingWeak w`, never by
inspecting `w` -- even though `w`'s shape is now visible, no law mentions it. -/
class ArcAPI (GF : BundledGFunctors) [Iris.InvGS_gen hlc GF]
    {E : Effect.{1}} (Hd : Handler E GF) (m : Mode) (T : Type) where
  new : T → ITree E (Arc T)
  deref : Arc T → ITree E T
  strong_count : Arc T → ITree E Int
  clone : Arc T → ITree E (Arc T)
  downgrade : Arc T → ITree E (Weak T)
  drop_strong : Arc T → ITree E Unit
  weak_clone : Weak T → ITree E (Weak T)
  weak_drop : Weak T → ITree E Unit
  weak_upgrade : Weak T → ITree E (Option (Arc T))
  weak_strong_count : Weak T → ITree E Int

  /-- `Weak::new()`. A value rather than an operation: making one allocates
  nothing. Every other weak handle a client meets is bound by the spec of the
  operation that produced it, so this is the only one the interface names. -/
  weak_new : Weak T
  /-- The `Arc` itself: `n` strong references and `k` weak ones. -/
  arcAuth : GName → Nat → Nat → IProp GF
  /-- One strong reference to `a`, whose payload is `v`. -/
  isArc : GName → Arc T → T → IProp GF
  /-- One weak reference, held through `w`. -/
  isWeak : GName → Weak T → T → IProp GF
  /-- `w` points at no control block. Persistent: it is a fact about `w` rather
  than a permission, which is what makes the dangling operations no-ops. -/
  isDanglingWeak : Weak T → IProp GF

  arcAuth_timeless γ n k : Timeless (arcAuth γ n k)
  isArc_timeless γ a v : Timeless (isArc γ a v)
  isWeak_timeless γ w v : Timeless (isWeak γ w v)
  isDanglingWeak_persistent w : Persistent (isDanglingWeak w)

  weak_new_dangling : ⊢ isDanglingWeak weak_new
  arcAuth_exclusive γ n₁ k₁ n₂ k₂ :
    iprop(arcAuth γ n₁ k₁ ∗ arcAuth γ n₂ k₂) ⊢@{IProp GF} iprop(False)
  isArc_agree γ a v v' :
    iprop(isArc γ a v ∗ isArc γ a v') ⊢@{IProp GF} iprop(⌜v = v'⌝)
  isArc_strong_pos γ a v n k :
    iprop(arcAuth γ n k ∗ isArc γ a v) ⊢@{IProp GF} iprop(⌜1 ≤ n⌝)
  isWeak_weak_pos γ w v n k :
    iprop(arcAuth γ n k ∗ isWeak γ w v) ⊢@{IProp GF} iprop(⌜1 ≤ k⌝)
  /-- A live weak reference is not a dangling one. -/
  isWeak_not_dangling γ w v :
    iprop(isWeak γ w v ∗ isDanglingWeak w) ⊢@{IProp GF} iprop(False)

  new_spec (v : T) (M : CoPset) :
    ⦃ emp ⦄ (new v) @ Hd ; m ; M
    ⦃ a, ∃ γ, arcAuth γ 1 0 ∗ isArc γ a v ⦄

  deref_spec (γ : GName) (a : Arc T) (v : T) (M : CoPset) :
    ⦃ isArc γ a v ⦄ (deref a) @ Hd ; m ; M
    ⦃ r, ⌜r = v⌝ ∗ isArc γ a v ⦄

  strong_count_spec (γ : GName) (a : Arc T) (v : T) :
    ⊢ isArc γ a v -∗
      ⟪ ∀ n k, arcAuth γ n k ⟫ Hd m (strong_count a) @ (∅ : CoPset)
      ⟪ arcAuth γ n k | RET (n : Int); isArc γ a v ⟫

  clone_spec (γ : GName) (a : Arc T) (v : T) :
    ⊢ isArc γ a v -∗
      ⟪ ∀ n k, arcAuth γ n k ⟫ Hd m (clone a) @ (∅ : CoPset)
      ⟪ arcAuth γ (n + 1) k | RET a; isArc γ a v ∗ isArc γ a v ⟫

  downgrade_spec (γ : GName) (a : Arc T) (v : T) :
    ⊢ isArc γ a v -∗
      ⟪ ∀ n k, arcAuth γ n k ⟫ Hd m (downgrade a) @ (∅ : CoPset)
      ⟪ arcAuth γ n (k + 1)
      | w, RET w; isArc γ a v ∗ isWeak γ w v ⟫

  drop_strong_spec (γ : GName) (a : Arc T) (v : T) :
    ⊢ isArc γ a v -∗
      ⟪ ∀ n k, arcAuth γ n k ⟫ Hd m (drop_strong a) @ (∅ : CoPset)
      ⟪ arcAuth γ (n - 1) (if n = 1 then k + 1 else k)
      | w, RET (); if n = 1 then isWeak γ w v else emp ⟫

  weak_clone_spec (γ : GName) (w : Weak T) (v : T) :
    ⊢ isWeak γ w v -∗
      ⟪ ∀ n k, arcAuth γ n k ⟫ Hd m (weak_clone w) @ (∅ : CoPset)
      ⟪ arcAuth γ n (k + 1) | RET w; isWeak γ w v ∗ isWeak γ w v ⟫

  /-- Upgrading a live weak retries its compare-and-swap, so it is only
  partially correct: a thread that keeps losing the race owes nothing. The
  dangling case below spins on nothing and so keeps the client's own mode. -/
  weak_upgrade_spec (γ : GName) (w : Weak T) (v : T) :
    ⊢ isWeak γ w v -∗
      ⟪ ∀ n k, arcAuth γ n k ⟫ Hd .part (weak_upgrade w) @ (∅ : CoPset)
      ⟪ arcAuth γ (if n = 0 then 0 else n + 1) k
      | a, RET (if n = 0 then none else some a)
      ; isWeak γ w v ∗ (if n = 0 then emp else isArc γ a v) ⟫

  weak_strong_count_spec (γ : GName) (w : Weak T) (v : T) :
    ⊢ isWeak γ w v -∗
      ⟪ ∀ n k, arcAuth γ n k ⟫ Hd m (weak_strong_count w) @ (∅ : CoPset)
      ⟪ arcAuth γ n k | RET (n : Int); isWeak γ w v ⟫

  weak_drop_spec (γ : GName) (w : Weak T) (v : T) :
    ⊢ isWeak γ w v -∗
      ⟪ ∀ n k, arcAuth γ n k ⟫ Hd m (weak_drop w) @ (∅ : CoPset)
      ⟪ arcAuth γ n (k - 1) | RET () ⟫

  dangling_clone_spec (w : Weak T) (M : CoPset) :
    ⦃ isDanglingWeak w ⦄ (weak_clone w) @ Hd ; m ; M
    ⦃ r, ⌜r = w⌝ ∗ isDanglingWeak w ⦄
  dangling_upgrade_spec (w : Weak T) (M : CoPset) :
    ⦃ isDanglingWeak w ⦄ (weak_upgrade w) @ Hd ; m ; M ⦃ r, ⌜r = none⌝ ⦄
  dangling_strong_count_spec (w : Weak T) (M : CoPset) :
    ⦃ isDanglingWeak w ⦄ (weak_strong_count w) @ Hd ; m ; M ⦃ r, ⌜r = 0⌝ ⦄
  dangling_drop_spec (w : Weak T) (M : CoPset) :
    ⦃ isDanglingWeak w ⦄ (weak_drop w) @ Hd ; m ; M ⦃ _r, emp ⦄

attribute [instance] ArcAPI.arcAuth_timeless ArcAPI.isArc_timeless
  ArcAPI.isWeak_timeless ArcAPI.isDanglingWeak_persistent

end Interface

end AeneasIris
