import AeneasIris.Arc
import AeneasIris.Tactics
import Iris.BI.Lib.Atomic
import AeneasIris.AtomicWpi

/-! # Logically atomic specs for `Arc` -/

unseal Aeneas.Std.Result

namespace AeneasIris.ArcLAT

open Iris BI Aeneas.Data.Coinductive
open AeneasIris AeneasIris.Heap AeneasIris.HeapAPI
open AeneasIris.AtomicWpi
open Aeneas.Std (StateE StepE Loc RustHeap RustEffect Result)
open AeneasIris.Arc
open AeneasIris.Step (stepH)

section

variable {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF] [HeapGS.{0} GF]
variable {E : Effect.{1}} [StateE RustHeap.{0} -< E] [StepE.{1} -< E]
variable {Hd : Handler E GF} [stateH heapInterp -<ₕ Hd]
variable {m : Mode} [stepH GF m -<ₕ Hd]

variable {T : Type} [Nonempty T] [ArcG GF T]

/-! ## Allocation -/

/-- **`new`.** Mirrors `new_spec`: one strong reference, no explicit weak ones. -/
theorem new_spec (v : T) (M : CoPset) :
    ⦃ emp ⦄ (new (E := E) v) @ Hd ; m ; M
    ⦃ a, ∃ γ, arcAuth (T := T) γ 1 0 ∗ isArc γ a v ⦄ := by
  sorry

/-! ## Strong references -/

/-- **`deref`.** Mirrors `deref_spec`: an ordinary read, no update involved. -/
theorem deref_spec (γ : GName) (a : Handle T) (v : T) (M : CoPset) :
    ⦃ isArc γ a v ⦄ (deref (E := E) a) @ Hd ; m ; M
    ⦃ r, ⌜r = v⌝ ∗ isArc γ a v ⦄ := by
  show _ ⊢ _
  iintro HA
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
      ⟪ ∀ n w, arcAuth (T := T) γ n w ⟫ Hd m (strong_count (E := E) a) @ (∅ : CoPset)
      ⟪ arcAuth (T := T) γ n w | RET (n : Int); isArc γ a v ⟫ := by
  /- Opens with `iaupd_commit HAU as ⟨n, w⟩ with HAuth`.  Then
     `arcAuth_strong_pos_keep` rules out `n = 0` -- at `n = 0, w = 0` `physical`
     owns no cells at all, so there would be nothing to load -- and
     `arcAuth_meta_agree_keep` identifies the authority's handle with `a`. -/
  sorry

/-- **`clone`.** Mirrors `clone_spec`: one more strong reference. -/
theorem clone_spec (γ : GName) (a : Handle T) (v : T) :
    ⊢ isArc γ a v -∗
      ⟪ ∀ n w, arcAuth (T := T) γ n w ⟫ Hd m (clone (E := E) a) @ (∅ : CoPset)
      ⟪ arcAuth (T := T) γ (n + 1) w | RET a; isArc γ a v ∗ isArc γ a v ⟫ := by
  iintro HA
  have hm : (⊤ : CoPset) \ (∅ : CoPset) = (⊤ : CoPset) := by simp
  simp only [atomicWpi, hm]
  iintro %Φ HAU
  simp only [Arc.clone]
  iapply (wpi_bind (H := Hd) _ _ _ ⊤)
  iapply (wpi_clear_mask (H := Hd) _ _ ⊤).mp
  ihave HAC := aupd_acc _ _ _ ⊤ ∅ ⊤ (by simp) $$ HAU
  imod HAC with ⟨%n, %m, HAuth, Hclose⟩
  sorry

/-- **`downgrade`.** Mirrors `downgrade_spec`: the strong reference is kept and a weak one is added. -/
theorem downgrade_spec (γ : GName) (a : Handle T) (v : T) :
    ⊢ isArc γ a v -∗
      ⟪ ∀ n w, arcAuth (T := T) γ n w ⟫ Hd m (downgrade (E := E) a) @ (∅ : CoPset)
      ⟪ arcAuth (T := T) γ n (w + 1)
      | RET (WeakHandle.live a); isArc γ a v ∗ isWeak γ a v ⟫ := by
  sorry

/-- **`dropStrong`.** Mirrors `drop_strong_spec`. -/
theorem dropStrong_spec (γ : GName) (a : Handle T) (v : T) :
    ⊢ isArc γ a v -∗
      ⟪ ∀ n w, arcAuth (T := T) γ n w ⟫ Hd m (dropStrong (E := E) a) @ (∅ : CoPset)
      ⟪ arcAuth (T := T) γ (n - 1) (if n = 1 then w + 1 else w)
      | RET (decide (n = 1)); if n = 1 then isWeak γ a v else emp ⟫ := by
  sorry

/-! ## Weak references -/

omit [Nonempty T] [ArcG GF T] in
theorem weakNew_spec : isDanglingWeak (weakNew (T := T)) := rfl

/-- **`weakClone`** on a live weak reference. Mirrors `weak_clone_spec`. -/
theorem weakClone_spec (γ : GName) (a : Handle T) (v : T) :
    ⊢ isWeak γ a v -∗
      ⟪ ∀ n w, arcAuth (T := T) γ n w ⟫
        Hd m (weakClone (E := E) (.live a)) @ (∅ : CoPset)
      ⟪ arcAuth (T := T) γ n (w + 1)
      | RET (WeakHandle.live a); isWeak γ a v ∗ isWeak γ a v ⟫ := by
  sorry

/-- **`weakUpgrade`** on a live weak reference. -/
theorem weakUpgrade_spec (γ : GName) (a : Handle T) (v : T) :
    ⊢ isWeak γ a v -∗
      ⟪ ∀ n w, arcAuth (T := T) γ n w ⟫
        Hd m (weakUpgrade (E := E) (.live a)) @ (∅ : CoPset)
      ⟪ arcAuth (T := T) γ (if n = 0 then 0 else n + 1) w
      | RET (if n = 0 then none else some a)
      ; isWeak γ a v ∗ (if n = 0 then emp else isArc γ a v) ⟫ := by
  sorry

/-- **`weakStrongCount`** on a live weak reference. -/
theorem weakStrongCount_spec (γ : GName) (a : Handle T) (v : T) :
    ⊢ isWeak γ a v -∗
      ⟪ ∀ n w, arcAuth (T := T) γ n w ⟫
        Hd m (weakStrongCount (E := E) (.live a)) @ (∅ : CoPset)
      ⟪ arcAuth (T := T) γ n w | RET (n : Int); isWeak γ a v ⟫ := by
  sorry

/-- **`weakDrop`** on a live weak reference. -/
theorem weakDrop_spec (γ : GName) (a : Handle T) (v : T) :
    ⊢ isWeak γ a v -∗
      ⟪ ∀ n w, arcAuth (T := T) γ n w ⟫
        Hd m (weakDrop (E := E) (.live a)) @ (∅ : CoPset)
      ⟪ arcAuth (T := T) γ n (w - 1) | RET () ⟫ := by
  sorry

/-! ## Dangling weak references -/

omit [Nonempty T] [ArcG GF T] in
theorem dangling_clone_spec (M : CoPset) :
    ⦃ emp ⦄ (weakClone (E := E) (T := T) .dangling) @ Hd ; m ; M
    ⦃ r, ⌜r = WeakHandle.dangling⌝ ⦄ := by
  show _ ⊢ _
  simp only [Arc.weakClone]
  iintro _
  iapply wpi_ret
  itrivial

omit [Nonempty T] [ArcG GF T] in
theorem dangling_upgrade_spec (M : CoPset) :
    ⦃ emp ⦄ (weakUpgrade (E := E) (T := T) .dangling) @ Hd ; m ; M
    ⦃ r, ⌜r = none⌝ ⦄ := by
  show _ ⊢ _
  simp only [Arc.weakUpgrade]
  iintro _
  iapply wpi_ret
  itrivial

omit [Nonempty T] [ArcG GF T] in
theorem dangling_strong_count_spec (M : CoPset) :
    ⦃ emp ⦄ (weakStrongCount (E := E) (T := T) .dangling) @ Hd ; m ; M
    ⦃ r, ⌜r = 0⌝ ⦄ := by
  show _ ⊢ _
  simp only [Arc.weakStrongCount]
  iintro _
  iapply wpi_ret
  itrivial

omit [Nonempty T] [ArcG GF T] in
theorem dangling_drop_spec (M : CoPset) :
    ⦃ emp ⦄ (weakDrop (E := E) (T := T) .dangling) @ Hd ; m ; M
    ⦃ r, ⌜r = ()⌝ ⦄ := by
  show _ ⊢ _
  simp only [Arc.weakDrop]
  iintro _
  iapply wpi_ret
  itrivial

end

end AeneasIris.ArcLAT
