import AeneasIris.Effects.Fail
import AeneasIris.Effects.Conc
import AeneasIris.Effects.Step
import AeneasIris.Effects.HeapAPI

/-! # The canonical handler for `RustEffect` -/

namespace AeneasIris.Rust

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

/-- The handler a translated Rust program runs under. -/
def rustH (m : Mode) : Handler RustEffect GF :=
  failH GF ⊕ₕ ConcH.{1} GF ⊕ₕ stepH.{1} GF m ⊕ₕ stateH heapInterp.{0}

/-! ## The four sub-effect inclusions -/

instance : ConcE.{1} -< RustEffect :=
  inferInstanceAs (ConcE.{1} -< (FailE.{1} ⊕ₑ ConcE.{1} ⊕ₑ StepE.{1} ⊕ₑ StateE RustHeap.{0}))

instance : StepE.{1} -< RustEffect :=
  inferInstanceAs (StepE.{1} -< (FailE.{1} ⊕ₑ ConcE.{1} ⊕ₑ StepE.{1} ⊕ₑ StateE RustHeap.{0}))

instance : StateE RustHeap.{0} -< RustEffect :=
  inferInstanceAs (StateE RustHeap.{0} -<
    (FailE.{1} ⊕ₑ ConcE.{1} ⊕ₑ StepE.{1} ⊕ₑ StateE RustHeap.{0}))

/-! ## The four handler inclusions -/

instance inH_failH (m : Mode) : failH GF -<ₕ rustH (GF := GF) m :=
  inferInstanceAs (failH GF -<ₕ
    (failH GF ⊕ₕ ConcH.{1} GF ⊕ₕ stepH.{1} GF m ⊕ₕ stateH heapInterp.{0}))

instance inH_ConcH (m : Mode) : ConcH.{1} GF -<ₕ rustH (GF := GF) m :=
  inferInstanceAs (ConcH.{1} GF -<ₕ
    (failH GF ⊕ₕ ConcH.{1} GF ⊕ₕ stepH.{1} GF m ⊕ₕ stateH heapInterp.{0}))

instance inH_stepH (m : Mode) : stepH.{1} GF m -<ₕ rustH (GF := GF) m :=
  inferInstanceAs (stepH.{1} GF m -<ₕ
    (failH GF ⊕ₕ ConcH.{1} GF ⊕ₕ stepH.{1} GF m ⊕ₕ stateH heapInterp.{0}))

instance inH_stateH (m : Mode) :
    stateH heapInterp.{0} -<ₕ rustH (GF := GF) m :=
  inferInstanceAs (stateH heapInterp.{0} -<ₕ
    (failH GF ⊕ₕ ConcH.{1} GF ⊕ₕ stepH.{1} GF m ⊕ₕ stateH heapInterp.{0}))

/-! ## The ambient handler -/

class Ambient {hlc : Iris.HasLC} (GF : BundledGFunctors) [Iris.InvGS_gen hlc GF]
    [HeapGS.{0} GF] where
  m : Mode
  handler : Handler RustEffect GF
  [failIn : failH GF -<ₕ handler]
  [concIn : ConcH.{1} GF -<ₕ handler]
  [stepIn : stepH.{1} GF m -<ₕ handler]
  [stateIn : stateH heapInterp.{0} -<ₕ handler]

attribute [instance] Ambient.failIn Ambient.concIn Ambient.stepIn Ambient.stateIn

/-- The ambient handler, with the binders the notation needs. -/
abbrev ambientH {hlc : Iris.HasLC} {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]
    [HeapGS.{0} GF] [Ambient (hlc := hlc) GF] : Handler RustEffect GF :=
  Ambient.handler hlc

/-- Partial correctness: every operation's step issues a `▷`, which is what -/
instance ambientLater : Ambient (hlc := hlc) GF where
  m := .part
  handler := rustH .part

/-! ## Total correctness implies partial correctness -/

instance rustH_total_wandH :
    wandH (rustH (GF := GF) .total) (rustH (GF := GF) .part) := by
  unfold rustH
  exact sumH_wandH (W₁ := wandH_refl _)
    (W₂ := sumH_wandH (W₁ := wandH_refl _)
      (W₂ := sumH_wandH (W₁ := Step.stepH_total_wandH GF) (W₂ := wandH_refl _)))

/-- The transport, on the weakest precondition. -/
theorem wpi_total_to_partial {α : Type} (t : ITree RustEffect α) (Φ : Post GF α)
    (M : CoPset) :
    wpi_mask GF (rustH .total) .total t Φ M ⊢ wpi_mask GF (rustH .part) .part t Φ M :=
  wpi_wandH (m₁ := .total) (m₂ := .part) BI.false_elim t Φ M

/-- The transport, on triples. -/
theorem iSpec_total_to_partial {α : Type} {P : IProp GF} {t : ITree RustEffect α}
    {Q : α → IProp GF} {M : CoPset}
    (h : ⦃ P ⦄ t @ (rustH (GF := GF) .total) ; .total ; M ⦃ v, Q v ⦄) :
    ⦃ P ⦄ t @ (rustH (GF := GF) .part) ; .part ; M ⦃ v, Q v ⦄ :=
  h.trans (wpi_total_to_partial t _ M)

end

end AeneasIris.Rust
