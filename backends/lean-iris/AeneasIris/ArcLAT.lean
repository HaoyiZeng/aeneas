import AeneasIris.Arc
import AeneasIris.Tactics
import Iris.BI.Lib.Atomic
import AeneasIris.AtomicWpi

/-!
# Logically atomic specs for `Arc`

Mirrors the `ArcAPI` contract of `MultiShot`. The shared resource is
`arcAuth γ n m` -- the control block and the two counts -- and every operation
that touches a count is stated as an atomic triple against it.

## Where this departs from `MultiShot`, and why

`deref` is **atomic here and pure there**. In the reference an `Arc` is a value
carrying its payload, so `deref` is a projection and needs nothing but
`isArc`. Ours is three heap locations, and `deref` is a real `load` of
`a.data` -- the cell that `arcAuth` owns while anyone still holds a reference.
Reading it therefore has to open the authority, which is exactly what an atomic
triple says. The alternative would be to give `isArc` a share of the payload
cell, but then the last `dropStrong` could not free it.

`strong_count` and `weakStrongCount` are atomic for the same reason: they read
`a.strong`, which lives in `arcAuth`.
-/

/- `iSpec` takes a `Result`, which is `@[irreducible]` outside the file that
defines it; every file here that states a triple unseals it for the same
reason. -/
unseal Aeneas.Std.Result

namespace AeneasIris.ArcLAT

open Iris BI Aeneas.Data.Coinductive
open AeneasIris AeneasIris.Heap AeneasIris.HeapAPI
open AeneasIris.AtomicWpi
open Aeneas.Std (StateE StepE Loc RustHeap RustEffect Result)
open AeneasIris.Arc

section

variable {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF] [HeapGS.{0} GF]
variable {T : Type} [Nonempty T] [ArcG GF T]

abbrev AH (GF : BundledGFunctors) [Iris.InvGS_gen hlc GF] [HeapGS.{0} GF] :
    Handler RustEffect GF := AeneasIris.RustHandler.rustH .later

/-! ## Allocation -/

/-- **`new`.** Mirrors `new_spec`: one strong reference, no explicit weak ones.

`arcAuth γ 1 0` and `isArc γ a v` are handed over together, because the client
that allocates is the one that owns the authority afterwards. -/
theorem new_spec (v : T) (M : CoPset) :
    ⦃ emp ⦄ (new (E := RustEffect) v) @ (AH GF) ; M
    ⦃ a, ∃ γ, arcAuth (T := T) γ 1 0 ∗ isArc γ a v ⦄ := by
  sorry

/-! ## Strong references -/

/-- **`deref`.** Mirrors `deref_spec`: an ordinary read, no update involved.

`isArc` carries a share of the payload cell, so dereferencing needs nothing
shared -- which is what makes `Arc` useful in the first place. The value read is
the one the metadata agrees on, so `RET v` is determined by `isArc γ a v`. -/
theorem deref_spec (γ : GName) (a : Handle T) (v : T) (M : CoPset) :
    ⦃ isArc γ a v ⦄ (deref (E := RustEffect) a) @ (AH GF) ; M
    ⦃ r, ⌜r = v⌝ ∗ isArc γ a v ⦄ := by
  show _ ⊢ _
  iintro HA
  /- `icases` does not see through a `def`, so unfold `isArc` first. -/
  simp only [Arc.isArc] at *
  icases HA with ⟨%q, Hmeta, Hstrong, Hpt⟩
  simp only [Arc.deref]
  istep
  isplitr
  itrivial
  iexists q
  iframe


/-- **`strong_count`.** Mirrors `weak_strong_count_spec`'s shape. -/
theorem strong_count_spec (γ : GName) (a : Handle T) (v : T) :
    ⊢ isArc γ a v -∗
      ⟪ ∀ n m, arcAuth (T := T) γ n m ⟫ (AH GF) (strong_count (E := RustEffect) a) @ (∅ : CoPset)
      ⟪ arcAuth (T := T) γ n m | RET (n : Int); isArc γ a v ⟫ := by
  sorry

/-- **`clone`.** Mirrors `clone_spec`: one more strong reference.

The returned handle is the same one -- an `Arc` clone shares the allocation,
which is the whole point -- so `RET a` mentions no binder. -/
theorem clone_spec (γ : GName) (a : Handle T) (v : T) :
    ⊢ isArc γ a v -∗
      ⟪ ∀ n m, arcAuth (T := T) γ n m ⟫ (AH GF) (clone (E := RustEffect) a) @ (∅ : CoPset)
      ⟪ arcAuth (T := T) γ (n + 1) m | RET a; isArc γ a v ∗ isArc γ a v ⟫ := by
  iintro HA
  have hm : (⊤ : CoPset) \ (∅ : CoPset) = (⊤ : CoPset) := by simp
  simp only [atomicWpi, hm]
  iintro %Φ HAU
  simp only [Arc.clone]
  iapply (wpi_bind (H := AH GF) _ _ _ ⊤)
  iapply (wpi_clear_mask (H := AH GF) _ _ ⊤).mp
  /- The linearisation point is the `faa`, so the update is opened here. -/
  ihave HAC := aupd_acc _ _ _ ⊤ ∅ ⊤ (by simp) $$ HAU
  imod HAC with ⟨%n, %m, HAuth, Hclose⟩
  /- TODO: the rest needs two algebraic laws that are not proved yet:
       - agreement: `arcAuth γ n m ∗ isArc γ a v ⊢ ⌜n > 0⌝`, and that the
         authority's existentials are exactly this `a` and `v`, so that
         `a.strong ↦ ·` can be extracted from `physical`;
       - allocation: `● res (some (a,v)) n m ⇝ ● res (some (a,v)) (n+1) m ∗ ◯ res none 1 0`,
         a local update on the strong `Credit`.
     With those, this closes by `wpi_faa (M := ∅)` and the commit branch of
     `Hclose`. -/
  sorry

/-- **`downgrade`.** Mirrors `downgrade_spec`: the strong reference is kept and a
weak one is added. -/
theorem downgrade_spec (γ : GName) (a : Handle T) (v : T) :
    ⊢ isArc γ a v -∗
      ⟪ ∀ n m, arcAuth (T := T) γ n m ⟫ (AH GF) (downgrade (E := RustEffect) a) @ (∅ : CoPset)
      ⟪ arcAuth (T := T) γ n (m + 1)
      | RET (WeakHandle.live a); isArc γ a v ∗ isWeak γ a v ⟫ := by
  sorry

/-- **`dropStrong`.** Mirrors `drop_strong_spec`.

The last strong reference out hands back a *weak* one. That is not bookkeeping
noise: Rust's `Arc` keeps a single weak reference on behalf of all the strong
ones, so that the control block outlives the payload. The payload is freed here;
the two counter cells go when the last weak leaves.

`n` is quantified plainly and the post says `n - 1`, rather than the
precondition asking for `arcAuth γ (n + 1) m`. The truncation is harmless
because `isArc` already entails `n > 0`, and stating it that way would make the
client produce a shape it has no reason to have -- the point of the linear token
is that the positivity travels with it. -/
theorem dropStrong_spec (γ : GName) (a : Handle T) (v : T) :
    ⊢ isArc γ a v -∗
      ⟪ ∀ n m, arcAuth (T := T) γ n m ⟫ (AH GF) (dropStrong (E := RustEffect) a) @ (∅ : CoPset)
      ⟪ arcAuth (T := T) γ (n - 1) (if n = 1 then m + 1 else m)
      | RET (decide (n = 1)); if n = 1 then isWeak γ a v else emp ⟫ := by
  sorry

/-! ## Weak references

The dangling weak reference is a sentinel: no allocation, no counts, so its
specs need no atomic update at all. -/

/- **`weakNew`.** -/
omit [Nonempty T] [ArcG GF T] in
theorem weakNew_spec : isDanglingWeak (weakNew (T := T)) := rfl

/-- **`weakClone`** on a live weak reference. Mirrors `weak_clone_spec`. -/
theorem weakClone_spec (γ : GName) (a : Handle T) (v : T) :
    ⊢ isWeak γ a v -∗
      ⟪ ∀ n m, arcAuth (T := T) γ n m ⟫
        (AH GF) (weakClone (E := RustEffect) (.live a)) @ (∅ : CoPset)
      ⟪ arcAuth (T := T) γ n (m + 1)
      | RET (WeakHandle.live a); isWeak γ a v ∗ isWeak γ a v ⟫ := by
  sorry

/-- **`weakUpgrade`** on a live weak reference. Mirrors `weak_upgrade_spec`.

Upgrading fails exactly when the payload is already gone (`n = 0`), which is the
one thing a weak reference is for. The weak reference itself survives either
way. -/
theorem weakUpgrade_spec (γ : GName) (a : Handle T) (v : T) :
    ⊢ isWeak γ a v -∗
      ⟪ ∀ n m, arcAuth (T := T) γ n m ⟫
        (AH GF) (weakUpgrade (E := RustEffect) (.live a)) @ (∅ : CoPset)
      ⟪ arcAuth (T := T) γ (if n = 0 then 0 else n + 1) m
      | RET (if n = 0 then none else some a)
      ; isWeak γ a v ∗ (if n = 0 then emp else isArc γ a v) ⟫ := by
  sorry

/-- **`weakStrongCount`** on a live weak reference. -/
theorem weakStrongCount_spec (γ : GName) (a : Handle T) (v : T) :
    ⊢ isWeak γ a v -∗
      ⟪ ∀ n m, arcAuth (T := T) γ n m ⟫
        (AH GF) (weakStrongCount (E := RustEffect) (.live a)) @ (∅ : CoPset)
      ⟪ arcAuth (T := T) γ n m | RET (n : Int); isWeak γ a v ⟫ := by
  sorry

/-- **`weakDrop`** on a live weak reference. Mirrors `weak_drop_spec`.

Dropping a weak reference says nothing about the strong count: weak and strong
references are released independently, and it is only when *both* counts reach
zero that the control block goes. -/
theorem weakDrop_spec (γ : GName) (a : Handle T) (v : T) :
    ⊢ isWeak γ a v -∗
      ⟪ ∀ n m, arcAuth (T := T) γ n m ⟫
        (AH GF) (weakDrop (E := RustEffect) (.live a)) @ (∅ : CoPset)
      ⟪ arcAuth (T := T) γ n (m - 1) | RET () ⟫ := by
  sorry

/-! ## Dangling weak references

Pure sentinels: nothing is allocated, so nothing is owned and no update is
needed. -/

/- **`weakClone`** on a dangling reference. -/
omit [Nonempty T] [ArcG GF T] in
theorem dangling_clone_spec (M : CoPset) :
    ⦃ emp ⦄ (weakClone (E := RustEffect) (T := T) .dangling) @ (AH GF) ; M
    ⦃ r, ⌜r = WeakHandle.dangling⌝ ⦄ := by
  show _ ⊢ _
  simp only [Arc.weakClone]
  iintro _
  iapply wpi_ret
  itrivial

/- **`weakUpgrade`** on a dangling reference always fails. -/
omit [Nonempty T] [ArcG GF T] in
theorem dangling_upgrade_spec (M : CoPset) :
    ⦃ emp ⦄ (weakUpgrade (E := RustEffect) (T := T) .dangling) @ (AH GF) ; M
    ⦃ r, ⌜r = none⌝ ⦄ := by
  show _ ⊢ _
  simp only [Arc.weakUpgrade]
  iintro _
  iapply wpi_ret
  itrivial

/- **`weakStrongCount`** on a dangling reference is `0`. -/
omit [Nonempty T] [ArcG GF T] in
theorem dangling_strong_count_spec (M : CoPset) :
    ⦃ emp ⦄ (weakStrongCount (E := RustEffect) (T := T) .dangling) @ (AH GF) ; M
    ⦃ r, ⌜r = 0⌝ ⦄ := by
  show _ ⊢ _
  simp only [Arc.weakStrongCount]
  iintro _
  iapply wpi_ret
  itrivial

/- **`weakDrop`** on a dangling reference does nothing. -/
omit [Nonempty T] [ArcG GF T] in
theorem dangling_drop_spec (M : CoPset) :
    ⦃ emp ⦄ (weakDrop (E := RustEffect) (T := T) .dangling) @ (AH GF) ; M
    ⦃ r, ⌜r = ()⌝ ⦄ := by
  show _ ⊢ _
  simp only [Arc.weakDrop]
  iintro _
  iapply wpi_ret
  itrivial

end

end AeneasIris.ArcLAT
