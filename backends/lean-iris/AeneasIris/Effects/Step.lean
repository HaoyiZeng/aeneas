import Aeneas.Std.Effects
import AeneasIris.Wpi
import AeneasIris.Rules
import Iris.Instances.Lib.Invariants

/-! # The `step` event — the later modality as a menu item -/

namespace AeneasIris.Step

open Iris BI Aeneas.Data.Coinductive
open Aeneas.Std (StepE)
open AeneasIris

/-! ## The effect -/

/-- Mark that a step has been taken. -/
def step.{u} {E : Effect.{u}} [StepE.{u} -< E] : ITree E PUnit.{u+1} :=
  Effect.trigger StepE.{u} .step

/-! ## The choice of modality -/

section Lat

variable {GF : BundledGFunctors}

/-- Apply the chosen modality. -/
def lat (m : Mode) (P : IProp GF) : IProp GF :=
  match m with
  | .total => P
  | .part => iprop% ▷ P

@[simp] theorem lat_identity (P : IProp GF) : lat .total P = P := rfl
@[simp] theorem lat_later (P : IProp GF) : lat .part P = iprop(▷ P) := rfl

theorem lat_mono (m : Mode) (P Q : IProp GF) :
    (P -∗ Q) ⊢ lat m P -∗ lat m Q := by
  cases m
  · simp only [lat_identity]
    iintro Hw HP
    iapply Hw $$ HP
  · simp only [lat_later]
    iintro Hw
    iapply BI.later_wand
    inext
    iexact Hw

/-- `lat_mono` in entailment form. -/
theorem lat_mono' (m : Mode) {P Q : IProp GF} (h : P ⊢ Q) :
    lat m P ⊢ lat m Q := by
  cases m
  · simpa only [lat_identity] using h
  · simpa only [lat_later] using BI.later_mono h

/-- `step` at an arbitrary value universe. -/
def stepP.{v, w} {E : Effect.{w}} [StepE.{w} -< E] : ITree E PUnit.{v+1} :=
  ITree.bind step fun _ => ITree.ret PUnit.unit

/-- Anything can be delayed. -/
theorem lat_intro (m : Mode) (P : IProp GF) : P ⊢ lat m P := by
  cases m
  · simp only [lat_identity]; exact .rfl
  · simp only [lat_later]; exact BI.later_intro
end Lat

/-! ## The handler -/

section Handler

variable (GF : BundledGFunctors) [Iris.InvGS_gen hlc GF]

def stepH.run.{u} (m : Mode) (i : StepE.I.{u}) (Ψ _Ψs : StepE.O i → IProp GF) :
    IProp GF :=
  match i with
  | .step => lat m (Ψ PUnit.unit)

def stepH.{u} (m : Mode) : Handler StepE.{u} GF where
  run := stepH.run GF m
  mono := by
    intro i Ψ Ψ' Ψs Ψs'
    cases i
    simp only [stepH.run]
    iintro Hw _
    iapply lat_mono
    iexact Hw

end Handler

/-! ## The rule -/

section Rule

variable {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]
variable {E : Effect.{w}} [StepE.{w} -< E] {Hd : Handler E GF} {m : Mode}
variable [stepH GF m -<ₕ Hd]

theorem wpi_step (Φ : Post GF PUnit.{w+1}) (M : CoPset) :
    lat m iprop(|={M}=> Φ PUnit.unit) ⊢ wpi_mask GF Hd m (step (E := E)) Φ M := by
  simp only [step]
  refine .trans ?_ (wpi_trigger (H := Hd) (E' := StepE) StepE.I.step Φ M
    (stepH GF m) (inH.embed _))
  iintro HΦ
  iapply Iris.fupd_mask_intro (E1 := M) (E2 := ∅) Iris.Std.LawfulSet.empty_subset
  iintro Hclose
  simp only [stepH, stepH.run]
  iapply lat_mono m _ _ $$ [Hclose] HΦ
  iintro HΦ'
  imod Hclose with _
  imod HΦ' with HΦ'
  imodintro
  iexact HΦ'

/-- `wpi_stepP`. -/
theorem wpi_stepP (Φ : Post GF PUnit.{v+1}) (M : CoPset) :
    lat m iprop(|={M}=> Φ PUnit.unit) ⊢ wpi_mask GF Hd m (stepP.{v, _} (E := E)) Φ M := by
  simp only [stepP]
  refine .trans ?_ (wpi_bind (H := Hd) step _ Φ M)
  refine .trans ?_ (wpi_step (m := m) (Hd := Hd) _ M)
  exact lat_mono' m (BIFUpdate.mono (wpi_ret PUnit.unit Φ M))

theorem wpi_stepThen {α : Type v} {P : IProp GF} (t : ITree E α) (Φ : Post GF α) (M : CoPset)
    (h : P ⊢ wpi_mask GF Hd m t Φ M) :
    lat m P ⊢ wpi_mask GF Hd m (do let _ ← stepP.{v, _}; t) Φ M := by
  show _ ⊢ wpi_mask GF Hd m (ITree.bind stepP fun _ => t) Φ M
  refine .trans ?_ (wpi_bind (H := Hd) stepP _ Φ M)
  refine .trans ?_ (wpi_stepP (m := m) (Hd := Hd) _ M)
  exact lat_mono' m (h.trans Iris.fupd_intro)

end Rule

/-! ## Total implies partial -/

instance stepH_total_wandH.{u} (GF : BundledGFunctors) [Iris.InvGS_gen hlc GF] :
    wandH (stepH.{u} GF .total) (stepH.{u} GF .part) where
  is_wandH e Ψ _ := by
    cases e
    simp only [stepH, stepH.run]
    exact lat_intro _ (Ψ PUnit.unit)

end AeneasIris.Step
