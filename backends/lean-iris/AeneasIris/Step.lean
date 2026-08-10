import Aeneas.Std.Effects
import AeneasIris.wpi
import AeneasIris.Rules
import Iris.Instances.Lib.Invariants

/-!
# The `step` event — the later modality as a menu item

`▷` is deliberately *not* built into `wpi`.  `wpi` is a least fixpoint and is
therefore termination-sensitive by default; `StepE` is the menu item that buys
termination-*insensitive* reasoning, by letting a handler issue a `▷` at each
marked point so that Löb induction becomes available.

Which modality a `step` issues is a parameter of the *handler*, not of the
weakest precondition: `stepH .identity` issues nothing and keeps the proof
termination-sensitive, `stepH .later` issues `▷`.

Ported from `src/step.v` of the "Program Logics à la Carte" artifact.
-/

namespace AeneasIris.Step

open Iris BI Aeneas.Data.Coinductive
open Aeneas.Std (StepE)
open AeneasIris

/-! ## The effect -/

-- The signature is `Aeneas.Std.StepE`; only the handler below needs Iris.

/-- Mark that a step has been taken.  The semantic analogue of `▷`. -/
def step {E : Effect} [StepE -< E] : ITree E Unit :=
  Effect.trigger StepE .step

/-! ## The choice of modality -/

inductive LaterModality where
  | identity
  | later
deriving DecidableEq

section Lat

variable {GF : BundledGFunctors}

/-- Apply the chosen modality. -/
def lat (m : LaterModality) (P : IProp GF) : IProp GF :=
  match m with
  | .identity => P
  | .later => iprop% ▷ P

@[simp] theorem lat_identity (P : IProp GF) : lat .identity P = P := rfl
@[simp] theorem lat_later (P : IProp GF) : lat .later P = iprop(▷ P) := rfl

theorem lat_mono (m : LaterModality) (P Q : IProp GF) :
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

/-- `lat_mono` in entailment form.

The wand version is what the proof mode wants; this one is what a `refine`
chain wants, where the two sides differ only under the modality. -/
theorem lat_mono' (m : LaterModality) {P Q : IProp GF} (h : P ⊢ Q) :
    lat m P ⊢ lat m Q := by
  cases m
  · simpa only [lat_identity] using h
  · simpa only [lat_later] using BI.later_mono h

/-- `step` at an arbitrary value universe.

`step` is `Unit`-valued, and `Unit` is in `Type 0`. A `do` block fixes a single
value universe, so a block that also carries a `Val.{u}` — which is in
`Type (u+1)`, because it packs a type as data — cannot bind an ordinary `step`.
`PUnit` is universe-polymorphic, so this version can be raised to meet whatever
the rest of the block needs, and the block stays in `do` notation.

The `ITree.bind` here is the one place the universes are crossed; everything
downstream is uniform. -/
def stepP.{v, w} {E : Effect.{w}} [StepE -< E] : ITree E PUnit.{v+1} :=
  ITree.bind step fun _ => ITree.ret PUnit.unit

/-- Anything can be delayed. -/
theorem lat_intro (m : LaterModality) (P : IProp GF) : P ⊢ lat m P := by
  cases m
  · simp only [lat_identity]; exact .rfl
  · simp only [lat_later]; exact BI.later_intro
end Lat

/-! ## The handler -/

section Handler

variable (GF : BundledGFunctors) [Iris.InvGS_gen hlc GF]

def stepH.run (m : LaterModality) (i : StepE.I) (Ψ _Ψs : StepE.O i → IProp GF) :
    IProp GF :=
  match i with
  | .step => lat m (Ψ ())

def stepH (m : LaterModality) : Handler StepE GF where
  run := stepH.run GF m
  mono := by
    intro i Ψ Ψ' Ψs Ψs'
    cases i
    simp only [stepH.run]
    iintro Hw _
    iapply lat_mono
    iexact Hw

end Handler

/-! ## The rule

`wpi_step` from `step.v:107`. Note the mask is **arbitrary** — unlike `yield`,
a `step` moves no invariants. The proof turns on taking the closing update
*before* going under `lat`, and carrying it in with `lat_mono`; going the other
way round would need the closing wand underneath a `▷`. -/

section Rule

variable {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]
variable {E : Effect} [StepE -< E] {Hd : Handler E GF} {m : LaterModality}
variable [inH (stepH GF m) Hd]

theorem wpi_step (Φ : Post GF Unit) (M : CoPset) :
    lat m iprop(|={M}=> Φ ()) ⊢ wpi_mask GF Hd (step (E := E)) Φ M := by
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

/-- `wpi_stepP`. Same rule as `wpi_step`, at whatever value universe the
surrounding `do` block is at. -/
theorem wpi_stepP (Φ : Post GF PUnit.{v+1}) (M : CoPset) :
    lat m iprop(|={M}=> Φ PUnit.unit) ⊢ wpi_mask GF Hd (stepP.{v, _} (E := E)) Φ M := by
  simp only [stepP]
  refine .trans ?_ (wpi_bind (H := Hd) step _ Φ M)
  refine .trans ?_ (wpi_step (m := m) (Hd := Hd) _ M)
  exact lat_mono' m (BIFUpdate.mono (wpi_ret PUnit.unit Φ M))

end Rule

end AeneasIris.Step
