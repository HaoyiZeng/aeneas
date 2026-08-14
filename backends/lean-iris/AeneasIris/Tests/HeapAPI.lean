import AeneasIris.Effects.HeapAPI
import AeneasIris.Tactics.Core

/-! Worked examples for the heap API. -/

namespace AeneasIris.Tests.HeapAPI

open AeneasIris.HeapAPI

open Iris BI Aeneas.Data.Coinductive
open AeneasIris AeneasIris.Heap
open Aeneas.Std (StateE StepE Loc AccessState Cell Val HMap RustHeap)
open scoped Aeneas.Std
open AeneasIris.Step (lat lat_intro stepH)

section Examples

variable {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF] [G : HeapGS.{0} GF]
variable {E : Effect.{1}} [StateE RustHeap.{0} -< E] [StepE.{1} -< E]
variable [Aeneas.Std.FailE.{1} -< E]
variable {Hd : Handler E GF} [stateH heapInterp.{0} -<ₕ Hd]
variable {m : Mode} [stepH GF m -<ₕ Hd]

example (l₁ l₂ : Loc) {M : CoPset} :
    iprop(l₁ ↦ (37 : Nat) ∗ l₂ ↦ ([true, false] : List Bool))
      ⊢ wpi_mask GF Hd m
          (do let a ← load (E := E) (T := Nat) l₁
              let b ← load (E := E) (T := List Bool) l₂
              return (a, b))
          (fun p => iprop(⌜p.1 = 37 ∧ p.2 = [true, false]⌝)) M := by
  iintro ⟨H₁, H₂⟩
  iapply (wpi_bind (H := Hd) (load (T := Nat) l₁) _ _ M)
  iapply (wpi_load (Hd := Hd) (m := m) l₁ (37 : Nat) (DFrac.own 1) (M := M))
  iapply (lat_intro m _)
  isplitl [H₁]
  · iexact H₁
  iintro _
  imodintro
  iapply (wpi_bind (H := Hd) (load (T := List Bool) l₂) _ _ M)
  iapply (wpi_load (Hd := Hd) (m := m) l₂ ([true, false] : List Bool) (DFrac.own 1) (M := M))
  iapply (lat_intro m _)
  isplitl [H₂]
  · iexact H₂
  iintro _
  imodintro
  iapply (wpi_ret' (H := Hd) _ _ M).mp
  imodintro
  ipureintro
  exact ⟨rfl, rfl⟩

example (l : Loc) {M : CoPset} :
    iprop(l ↦ (1 : Nat))
      ⊢ wpi_mask GF Hd m (cas (E := E) l (1 : Nat) 2)
          (fun b => iprop(⌜b = true⌝ ∗ l ↦ (2 : Nat))) M := by
  iintro Hl
  iapply (wpi_cas_succ (Hd := Hd) (m := m) l 1 2 (M := M))
  iapply (lat_intro m _)
  isplitl [Hl]
  · iexact Hl
  iintro Hl'
  imodintro
  isplitr [Hl']
  · ipureintro; rfl
  iexact Hl'

example (l : Loc) {M : CoPset} :
    iprop(l ↦ (1 : Nat))
      ⊢ wpi_mask GF Hd m (faa (E := E) l (1 : Nat))
          (fun v => iprop(⌜v = 1⌝ ∗ l ↦ (2 : Nat))) M := by
  iintro Hl
  iapply (wpi_faa (Hd := Hd) (m := m) l (1 : Nat) 1 (M := M))
  iapply (lat_intro m _)
  isplitl [Hl]
  · iexact Hl
  iintro Hl'
  imodintro
  isplitr [Hl']
  · ipureintro; rfl
  iexact Hl'

noncomputable example (l₁ l₂ : Loc) : ITree E PUnit.{1} := do
  let a : Nat ← load l₁
  let b : List Bool ← load l₂
  let _ ← store l₁ (a + b.length)
  store l₂ (b ++ [true])

/--
error: istep: the goal is a `wpi_mask`, but `irule` could not read it, so no rule fired.

irule said:
irule: the goal is not a `wpi_mask` (head @ProofMode.Entails')

Usually this means the reified proof-mode context went stale: a `have`, `rcases`, `cases`, `split` or `rw` between proof-mode steps rebuilds the goal and invalidates it, even though the goal still prints correctly. If there is such a step above, hoist it above the opening `iintro`, or destructure inside the proof-mode tactic instead (e.g. `iintro ⟨a, b⟩`); `simp only` is safe.

If there is no such step, do not go looking for one — this message reports what `irule` could not do, not why.
-/
#guard_msgs in
example (l : Loc) {M : CoPset} :
    iprop(l ↦ (1 : Nat))
      ⊢ wpi_mask GF Hd m (cas (E := E) l (1 : Nat) 2)
          (fun b => iprop(⌜b = true⌝ ∗ l ↦ (2 : Nat))) M := by
  iintro Hl
  have stale : (1 : Nat) + 1 = 2 := rfl
  istep

end Examples

end AeneasIris.Tests.HeapAPI
