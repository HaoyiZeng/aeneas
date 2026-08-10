import AeneasIris.ISpec
import AeneasIris.Concurrency
import AeneasIris.Fail
import Aeneas.Tactic.Step.Step

/-!
# Tests

1. **`iSpec` is the proof-mode goal.** Not up to a lemma — up to `rfl`.
2. **The lifting composes.** An Aeneas `⦃⦄` lemma is used inside a `wpi` proof
   without restating it, and the caller's resources survive the call.

Heap regressions live separately; they are parked while `AeneasIris.HeapRules`
grows the `yield` between the two phases of a non-atomic access.
-/

namespace AeneasIris.Test

open Iris BI Aeneas.Data.Coinductive
open AeneasIris
open Aeneas.Std (Result RustEffect)

unseal Aeneas.Std.Result

section StepOnISpec

variable {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]
variable {H : Handler RustEffect GF}

/-- A stand-in for a translated Rust function, with an Aeneas-style spec. -/
def twice (n : Nat) : Result Nat := .ok (2 * n)

@[step]
theorem twice_spec (n : Nat) : Aeneas.Std.WP.spec (twice n) (fun r => r = 2 * n) :=
  .ret _ _ rfl

/-- The lifting on its own. -/
example (n : Nat) (M : CoPset) :
    iSpecT H (twice n) (fun v => iprop(⌜v = 2 * n⌝)) M :=
  spec_to_iSpecT (twice_spec n)

/-- **The point of the whole exercise.** Two calls to an Aeneas function,
sequenced with `do`. `step` recognises the `Bind.bind`, finds `twice_spec` in
the `@[step]` database, lifts it through `spec_to_iSpecT`, and applies
`iSpecT_bind'` — the `⦃⦄` lemma is reused, not restated. -/
example (n : Nat) (M : CoPset) :
    iSpecT H (do let a ← twice n; let b ← twice a; pure b) (λ _ => iprop(True ∗ True)) M := by
  step
  step
  simp
  iintro
  imodintro
  itrivial

/-! ### The same, at an arbitrary signature

`iSpecT` is what a mixed program needs: the handler is over some `E` that merely
*contains* `RustEffect`, so the very same Aeneas `⦃⦄` lemmas remain reusable
next to rules for effects Aeneas knows nothing about. -/

section Poly

variable {E : Effect} [RustEffect -< E] {HE : Handler E GF}

example (n : Nat) (M : CoPset) :
    iSpecT HE (twice n) (fun v => iprop(⌜v = 2 * n⌝)) M :=
  spec_to_iSpecT (twice_spec n)

example (n : Nat) (M : CoPset) :
    iSpecT HE (do let a ← twice n; let b ← twice a; pure b)
      (λ _ => iprop(True ∗ True)) M := by
  step
  step
  simp
  iintro
  imodintro
  itrivial

end Poly

end StepOnISpec

/-! ## A concrete mixed signature

`EE` is what a real client assembles: the effects Aeneas emits, plus the ones
only the program logic knows about. `RustEffect -< EE` is what `iSpecT` asks
for, so every Aeneas `⦃⦄` lemma stays available; `ConcE -< EE` is what the
concurrency rules ask for. Neither side had to be told about the other. -/

section Mixed

open Aeneas.Std (ConcE)
open AeneasIris.ConcE (ConcH yield wpi_yield spawn wpi_spawn)
open AeneasIris.Fail (failH)

abbrev EE : Effect := RustEffect ⊕ₑ ConcE

variable {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]

abbrev HEE (GF : BundledGFunctors) [Iris.InvGS_gen hlc GF] : Handler EE GF :=
  failH GF ⊕ₕ ConcH GF

/-- Aeneas code alone, but under the *combined* handler. -/
example (n : Nat) (M : CoPset) :
    iSpecT (HEE GF) (twice n) (fun v => iprop(⌜v = 2 * n⌝)) M :=
  spec_to_iSpecT (twice_spec n)

/-- Aeneas, then a `yield`, then Aeneas again.

The program is an `ITree EE`, so the goal is a bare `wpi_mask`, not an
`iSpecT`. `wpi_bind` peels off the leading Aeneas block; the residual goal is
*definitionally* an `iSpecT`, which is what lets `step` fire on it and reuse
`twice_spec`. -/
example (n : Nat) :
    ⊢ wpi_mask GF (HEE GF)
        (do let a ← ITree.translate (twice n)
            yield
            let b ← ITree.translate (twice a)
            pure b)
        (fun v => iprop(⌜v = 4 * n⌝)) ⊤ := by
  step_aeneas
  /- The `yield`: a rule the Aeneas backend knows nothing about, applied to the
  same goal, under the same handler. -/
  refine .trans ?_ (wpi_bind (H := HEE GF) _ _ _ _)
  refine .trans ?_ (wpi_yield (H := HEE GF) GF _)
  /- Back to Aeneas, and `step` again. -/
  step_aeneas
  refine .trans ?_ (wpi_ret (H := HEE GF) _ _ _)
  exact BI.pure_intro (by simp [*]; ring)

/-- `spawn`, whose child thread is itself Aeneas code.

The forked tree is an `ITree EE` obligation discharged the same way — peel with
`wpi_bind`, `show` it is an `iSpecT`, `step`. Nothing about the child being a
*thread* changes how the Aeneas lemma is used. -/
example (n : Nat) :
    ⊢ wpi_mask GF (HEE GF)
        (do spawn (do let _ ← ITree.translate (twice n); pure ())
            let b ← ITree.translate (twice n)
            pure b)
        (fun v => iprop(⌜v = 2 * n⌝)) ⊤ := by
  refine .trans ?_ (wpi_bind (H := HEE GF) _ _ _ _)
  refine .trans ?_ (wpi_spawn (H := HEE GF) GF _ _ _)
  refine BI.emp_sep.2.trans (BI.sep_mono ?_ ?_)
  · /- The parent continues: Aeneas again. -/
    step_aeneas
    refine .trans ?_ (wpi_ret (H := HEE GF) _ _ _)
    exact BI.pure_intro (by simp [*])
  · /- The child thread. -/
    step_aeneas
    refine .trans ?_ (wpi_ret (H := HEE GF) _ _ _)
    exact BI.pure_intro trivial

/-! ### With a non-trivial Iris precondition

The shape the user actually wants: `{P} t {Q}` with `P` a real separation-logic
assertion, `iintro`'d into the spatial context, and `istep` consuming the
Aeneas calls while `P` is framed across them untouched. -/

example (n : Nat) (Pr : IProp GF) :
    Pr ⊢ wpi_mask GF (HEE GF)
      (ITree.translate ((do let a ← twice n; twice a : Result Nat)))
      (fun v => iprop(⌜v = 4 * n⌝ ∧ Pr)) ⊤ := by
  istep
  istep
  iintro HP
  isplit
  · ipureintro; simp [*]; ring
  · iexact HP

end Mixed

end AeneasIris.Test
