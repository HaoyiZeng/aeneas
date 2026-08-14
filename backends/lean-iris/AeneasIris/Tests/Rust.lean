import AeneasIris.Rust

/-! Each rule, applied at the concrete `rustH` handler with nothing supplied but the handler: evidence that the… -/

namespace AeneasIris.Tests.Rust

open AeneasIris.Rust

open Iris BI Aeneas.Data.Coinductive
open AeneasIris
open AeneasIris.Fail (failH)
open AeneasIris.Conc (ConcH)
open AeneasIris.Step (stepH lat lat_mono)
open AeneasIris.Heap (stateH heapInterp HeapGS)
open AeneasIris.HeapAPI (pointsTo load alloc)
open Aeneas.Std (FailE ConcE StepE StateE RustEffect RustHeap Loc)

section

variable {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF] [HeapGS.{0} GF]

/-! ## The rules, at the concrete handler The `inH` instances above are only evidence that the *constraints* ar… -/

section Instantiation

variable {m : Mode} {M : CoPset}

/-- A heap read. -/
example (l : Loc) (v : Nat) (dq : DFrac) (Φ : Post GF Nat) :
    lat m iprop(l ↦{dq} v ∗ (l ↦{dq} v -∗ |={M}=> Φ v))
      ⊢ wpi_mask GF (rustH m) m (HeapAPI.load (E := RustEffect) (T := Nat) l) Φ M :=
  HeapAPI.wpi_load (Hd := rustH m) l v dq

/-- A step on its own. -/
example (Φ : Post GF PUnit.{2}) :
    lat m iprop(|={M}=> Φ PUnit.unit)
      ⊢ wpi_mask GF (rustH m) m (Step.step (E := RustEffect)) Φ M :=
  Step.wpi_step (Hd := rustH m) Φ M

/-- A scheduling point. -/
example (Φ : Post GF PUnit.{2}) :
    iprop(Φ PUnit.unit) ⊢ wpi_mask GF (rustH m) m (Conc.yield (E := RustEffect)) Φ ⊤ :=
  Conc.wpi_yield GF (H := rustH m) Φ

/-- Failure. The one rule that consumes rather than establishes. -/
example (e : Aeneas.Std.Error) (Φ : Post GF Nat) :
    iprop(|={M, ∅}=> False)
      ⊢ wpi_mask GF (rustH m) m (Fail.fail (E := RustEffect) e) Φ M :=
  Fail.wpi_fail (Hd := rustH m) e Φ M

/-- All four in one program: allocate, step, read back, yield. -/
example (Φ : Post GF Nat) :
    lat m iprop(∀ l, l ↦ (7 : Nat) -∗ |={⊤}=>
        wpi_mask GF (rustH m) m (HeapAPI.load (E := RustEffect) (T := Nat) l) Φ ⊤)
      ⊢ wpi_mask GF (rustH m) m
          (do let l ← HeapAPI.alloc (E := RustEffect) (7 : Nat)
              HeapAPI.load (T := Nat) l) Φ ⊤ := by
  refine .trans ?_
    (wpi_bind (H := rustH m) (HeapAPI.alloc (E := RustEffect) (7 : Nat)) _ Φ ⊤)
  exact HeapAPI.wpi_alloc (Hd := rustH m) (m := m) (7 : Nat) (M := ⊤)

end Instantiation

end

end AeneasIris.Tests.Rust
