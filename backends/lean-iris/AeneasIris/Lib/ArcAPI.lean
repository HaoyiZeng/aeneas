import AeneasIris.Tactics
import AeneasIris.AtomicWpi
import Iris.BI.Lib.Atomic

/-! # The `Arc` interface -/

namespace AeneasIris.ArcAPI

open Iris BI Aeneas.Data.Coinductive
open AeneasIris AeneasIris.AtomicWpi

section Interface

variable {hlc : Iris.HasLC}

/-- A reference-counted pointer to `T`, as a menu of operations, three abstract
predicates, and the laws relating them.

Generic in the effect row `E`, the handler `Hd` and the `Mode`, so a client
programs against the interface at whatever language it is itself written in. The
carrier types are `outParam`s: an implementation chooses them, and a client names
them without spelling out which implementation it meant.

The shared resource is `arcAuth γ n w` -- the control block and the two counts --
and every operation that moves a count is stated as an atomic triple against it.
`deref` is the exception: `isArc` carries a share of the payload, so reading it
needs nothing shared, which is the whole point of an `Arc`. -/
class ArcAPI (GF : BundledGFunctors) [Iris.InvGS_gen hlc GF]
    {E : Effect.{1}} (Hd : Handler E GF) (m : Mode) (T : Type)
    (Handle WeakHandle : outParam Type) where
  new : T → ITree E Handle
  deref : Handle → ITree E T
  strong_count : Handle → ITree E Int
  clone : Handle → ITree E Handle
  downgrade : Handle → ITree E WeakHandle
  dropStrong : Handle → ITree E Bool
  weakClone : WeakHandle → ITree E WeakHandle
  weakDrop : WeakHandle → ITree E Unit
  weakUpgrade : WeakHandle → ITree E (Option Handle)
  weakStrongCount : WeakHandle → ITree E Int

  /-- The weak handle that points at nothing, and the one a `downgrade` returns.

  Exposed rather than existentially quantified in `downgrade_spec`, for the same
  reason the lock exposes its guards: the handle *is* determined by the `Arc` in
  any implementation. -/
  weakNew : WeakHandle
  mkWeak : Handle → WeakHandle

  /-- The `Arc` itself: `n` strong references and `w` weak ones. -/
  arcAuth : GName → Nat → Nat → IProp GF
  /-- One strong reference to `a`, whose payload is `v`. -/
  isArc : GName → Handle → T → IProp GF
  /-- One weak reference. -/
  isWeak : GName → Handle → T → IProp GF

  isArc_strong_pos γ a v n w :
    iprop(arcAuth γ n w ∗ isArc γ a v) ⊢@{IProp GF} iprop(⌜1 ≤ n⌝)
  isWeak_weak_pos γ a v n w :
    iprop(arcAuth γ n w ∗ isWeak γ a v) ⊢@{IProp GF} iprop(⌜1 ≤ w⌝)

  new_spec (v : T) (M : CoPset) :
    ⦃ emp ⦄ (new v) @ Hd ; m ; M
    ⦃ a, ∃ γ, arcAuth γ 1 0 ∗ isArc γ a v ⦄

  deref_spec (γ : GName) (a : Handle) (v : T) (M : CoPset) :
    ⦃ isArc γ a v ⦄ (deref a) @ Hd ; m ; M
    ⦃ r, ⌜r = v⌝ ∗ isArc γ a v ⦄

  strong_count_spec (γ : GName) (a : Handle) (v : T) :
    ⊢ isArc γ a v -∗
      ⟪ ∀ n w, arcAuth γ n w ⟫ Hd m (strong_count a) @ (∅ : CoPset)
      ⟪ arcAuth γ n w | RET (n : Int); isArc γ a v ⟫

  clone_spec (γ : GName) (a : Handle) (v : T) :
    ⊢ isArc γ a v -∗
      ⟪ ∀ n w, arcAuth γ n w ⟫ Hd m (clone a) @ (∅ : CoPset)
      ⟪ arcAuth γ (n + 1) w | RET a; isArc γ a v ∗ isArc γ a v ⟫

  downgrade_spec (γ : GName) (a : Handle) (v : T) :
    ⊢ isArc γ a v -∗
      ⟪ ∀ n w, arcAuth γ n w ⟫ Hd m (downgrade a) @ (∅ : CoPset)
      ⟪ arcAuth γ n (w + 1)
      | RET (mkWeak a); isArc γ a v ∗ isWeak γ a v ⟫

  dropStrong_spec (γ : GName) (a : Handle) (v : T) :
    ⊢ isArc γ a v -∗
      ⟪ ∀ n w, arcAuth γ n w ⟫ Hd m (dropStrong a) @ (∅ : CoPset)
      ⟪ arcAuth γ (n - 1) (if n = 1 then w + 1 else w)
      | RET (decide (n = 1)); if n = 1 then isWeak γ a v else emp ⟫

  weakClone_spec (γ : GName) (a : Handle) (v : T) :
    ⊢ isWeak γ a v -∗
      ⟪ ∀ n w, arcAuth γ n w ⟫ Hd m (weakClone (mkWeak a)) @ (∅ : CoPset)
      ⟪ arcAuth γ n (w + 1)
      | RET (mkWeak a); isWeak γ a v ∗ isWeak γ a v ⟫

  weakUpgrade_spec (γ : GName) (a : Handle) (v : T) :
    ⊢ isWeak γ a v -∗
      ⟪ ∀ n w, arcAuth γ n w ⟫ Hd m (weakUpgrade (mkWeak a)) @ (∅ : CoPset)
      ⟪ arcAuth γ (if n = 0 then 0 else n + 1) w
      | RET (if n = 0 then none else some a)
      ; isWeak γ a v ∗ (if n = 0 then emp else isArc γ a v) ⟫

  weakStrongCount_spec (γ : GName) (a : Handle) (v : T) :
    ⊢ isWeak γ a v -∗
      ⟪ ∀ n w, arcAuth γ n w ⟫ Hd m (weakStrongCount (mkWeak a)) @ (∅ : CoPset)
      ⟪ arcAuth γ n w | RET (n : Int); isWeak γ a v ⟫

  weakDrop_spec (γ : GName) (a : Handle) (v : T) :
    ⊢ isWeak γ a v -∗
      ⟪ ∀ n w, arcAuth γ n w ⟫ Hd m (weakDrop (mkWeak a)) @ (∅ : CoPset)
      ⟪ arcAuth γ n (w - 1) | RET () ⟫

  dangling_clone_spec (M : CoPset) :
    ⦃ emp ⦄ (weakClone weakNew) @ Hd ; m ; M ⦃ r, ⌜r = weakNew⌝ ⦄
  dangling_upgrade_spec (M : CoPset) :
    ⦃ emp ⦄ (weakUpgrade weakNew) @ Hd ; m ; M ⦃ r, ⌜r = none⌝ ⦄
  dangling_strong_count_spec (M : CoPset) :
    ⦃ emp ⦄ (weakStrongCount weakNew) @ Hd ; m ; M ⦃ r, ⌜r = 0⌝ ⦄
  dangling_drop_spec (M : CoPset) :
    ⦃ emp ⦄ (weakDrop weakNew) @ Hd ; m ; M ⦃ r, ⌜r = ()⌝ ⦄

end Interface

end AeneasIris.ArcAPI
