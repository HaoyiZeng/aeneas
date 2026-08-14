import AeneasIris.AtomicWpi

/-! Round-trip tests for the logically-atomic-triple notation: the three optional groups -- post-binders, `RET`… -/

namespace AeneasIris.Tests.AtomicWpi

open AeneasIris.AtomicWpi

open Iris BI Aeneas.Data.Coinductive AeneasIris

variable {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]

/-! ## Round-trip tests The three optional groups -- post-binders, `RET`-binders, `POST` -- are what the refere… -/

section Tests
variable {Eff : Effect.{0}} (Hd : Handler Eff GF) (m : Mode)
variable {S V : Type} (inv : S → V → IProp GF) (t : ITree Eff Nat)

/-- info: ⟪ ∀ s v, inv s v ⟫ Hd m t @ ⊤ ⟪ ∃ w, inv s w | r, RET r; inv s v ⟫ : IProp GF -/
#guard_msgs in
#check (⟪ ∀ s v, inv s v ⟫ Hd m t @ ⊤ ⟪ ∃ w, inv s w | r, RET r; inv s v ⟫)

/-- info: ⟪ ∀ s v, inv s v ⟫ Hd m t @ ⊤ ⟪ ∃ w, inv s w | RET 0 ⟫ : IProp GF -/
#guard_msgs in
#check (⟪ ∀ s v, inv s v ⟫ Hd m t @ ⊤ ⟪ ∃ w, inv s w | RET 0 ⟫)

/-- info: ⟪ ∀ s v, inv s v ⟫ Hd m t @ ⊤ ⟪ inv s v | RET 0 ⟫ : IProp GF -/
#guard_msgs in
#check (⟪ ∀ s v, inv s v ⟫ Hd m t @ ⊤ ⟪ inv s v | RET 0 ⟫)

end Tests

end AeneasIris.Tests.AtomicWpi
