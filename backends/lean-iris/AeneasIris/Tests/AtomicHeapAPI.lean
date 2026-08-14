import AeneasIris.Effects.AtomicHeapAPI
import AeneasIris.Tactics.Core

/-! Worked examples for the concurrent heap API and its one-shot triples. -/

namespace AeneasIris.Tests.AtomicHeapAPI

open Iris BI Aeneas.Data.Coinductive
open AeneasIris AeneasIris.Heap AeneasIris.HeapAPI AeneasIris.AtomicHeapAPI
open Aeneas.Std (StateE StepE Loc Val RustHeap)
open scoped Aeneas.Std
open scoped AeneasIris.OneShotWpi

section Examples

variable {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF] [G : HeapGS.{0} GF]
variable {E : Effect.{1}} [StateE RustHeap.{0} -< E] [StepE.{1} -< E]
variable [Aeneas.Std.ConcE.{1} -< E]
variable {Hd : Handler E GF} [stateH heapInterp.{0} -<ₕ Hd] [Conc.ConcH GF -<ₕ Hd]
variable {m : Mode} [AeneasIris.Step.stepH GF m -<ₕ Hd]

/-- Exclusive ownership: each `load` yields, so another thread runs in between --
but it cannot touch `l`, which this thread owns.  Both reads therefore return the
same value, and the proof is the sequential one. -/
example (l : Loc) :
    ⦃ l ↦ (7 : Nat) ⦄
      (do let a ← AtomicHeapAPI.load (E := E) (T := Nat) l
          let b ← AtomicHeapAPI.load (E := E) (T := Nat) l
          ITree.ret (a + b)) @ Hd ; m ; ⊤
      ⦃ r, ⌜r = 14⌝ ∗ l ↦ (7 : Nat) ⦄ := by
  iintro Hl
  istep as ⟨a, Ha⟩
  istep as ⟨b, Hb⟩
  istep
  isplitr [Hb]
  · ipureintro; rfl
  · iexact Hb

/-- Shared ownership: `l` lives in an invariant, so another thread may write to it
at any point.  The one-shot triple hands the caller an update; `iinv_atomic` opens
the invariant into it, and the closer `Hcl` and the mask witness `Hback` are
discharged once the cell has been handed back. -/
example (l : Loc) (N : Namespace) :
    ⊢ Iris.inv N iprop(∃ v : Nat, l ↦ v) -∗
      wpi_mask GF Hd m (AtomicHeapAPI.load (E := E) (T := Nat) l)
        (fun _ => iprop(True)) ⊤ := by
  iintro #Hinv
  iapply (AeneasIris.OneShotWpi.IASpec.wand
    (AtomicHeapAPI.load_spec (E := E) (T := Nat) l (DFrac.own 1)) _) $$ []
  · itrivial
  iinv_atomic Hinv with ⟨⟨%v, Hl⟩, Hcl⟩ back Hback
  iexists v
  isplitl [Hl]
  · iexact Hl
  · imodintro
    iintro %_y Hl'
    imod Hback
    ihave HI : iprop(∃ w : Nat, l ↦ w) $$ [Hl']
    · iexists v
      iexact Hl'
    ispecialize Hcl $$ HI
    imod Hcl
    imodintro
    iintro %_z _
    itrivial

end Examples

end AeneasIris.Tests.AtomicHeapAPI
