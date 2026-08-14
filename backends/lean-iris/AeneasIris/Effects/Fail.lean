import Aeneas.Std.Primitives
import AeneasIris.Wpi
import AeneasIris.Rules
import Iris.Instances.Lib.Invariants

/-! # The failure handler -/

namespace AeneasIris.Fail

open Iris BI Aeneas.Data.Coinductive
open Aeneas.Std (FailE RustEffect Error)
open AeneasIris

section Handler

variable (GF : BundledGFunctors) [Iris.InvGS_gen hlc GF]

/-- Failure is unprovable. -/
def failH.run.{u} (_i : FailE.I.{u}) (_Ψ _Ψs : FailE.O _i → IProp GF) : IProp GF :=
  iprop(False)

def failH.{u} : Handler FailE.{u} GF where
  run := failH.run GF
  mono := by
    intro i Ψ Ψ' Ψs Ψs'
    simp only [failH.run]
    iintro _ _ H
    iexact H

end Handler

section Rules

variable {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]
variable {E : Effect.{u}} [FailE.{u} -< E] {Hd : Handler E GF} [failH.{u} GF -<ₕ Hd]

/-- `fail` as a program: trigger the event, then eliminate its impossible answer. -/
def fail {α : Type _} (e : Error) : ITree E α :=
  ITree.bind (Effect.trigger FailE.{u} (FailE.I.fail e)) (fun o => PEmpty.elim o)

/-- `wpi_fail`. -/
theorem wpi_fail {α : Type _} (e : Error) (Φ : Post GF α) (M : CoPset) :
    iprop(|={M, ∅}=> False) ⊢ wpi_mask GF Hd m (fail (E := E) e) Φ M := by
  simp only [fail]
  refine .trans ?_ (wpi_bind (H := Hd) _ _ Φ M)
  refine .trans ?_ (wpi_trigger' (H' := failH.{u} GF) (FailE.I.fail e) _ M)
  simp only [failH, failH.run]
  exact .rfl

end Rules

/-! ## The alternative -/

end AeneasIris.Fail
