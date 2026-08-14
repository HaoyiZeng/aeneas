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
at any point and the value read is not predictable.  What *is* predictable is
anything the invariant maintains -- here positivity -- and that is what a
logically atomic specification lets the caller conclude. -/
example (l : Loc) (N : Namespace) :
    ⊢ Iris.inv N iprop(∃ v : Nat, l ↦ v ∗ ⌜0 < v⌝) -∗
      wpi_mask GF Hd m (AtomicHeapAPI.load (E := E) (T := Nat) l)
        (fun r => iprop(⌜0 < r⌝)) ⊤ := by
  iintro #Hinv
  istep
  iinv_atomic Hinv with ⟨⟨%v, Hl, %hv⟩, Hcl⟩ back Hback
  iexists v
  isplitl [Hl]
  · iexact Hl
  · imodintro
    iintro %_y Hl'
    imod Hback
    ihave HI : iprop(∃ w : Nat, l ↦ w ∗ ⌜0 < w⌝) $$ [Hl']
    · iexists v
      isplitl [Hl']
      · iexact Hl'
      · ipureintro; exact hv
    ispecialize Hcl $$ HI
    imod Hcl
    imodintro
    iintro %_z _
    ipureintro
    exact hv

/-- A shared compare-and-swap.  The invariant keeps the cell positive; the CAS
either succeeds, installing a value the caller must show keeps that true, or
fails and changes nothing.  Either way the invariant is restored, so a caller
learns the outcome without ever knowing what the cell held. -/
example (l : Loc) (N : Namespace) (old new : Nat) (hnew : 0 < new) :
    ⊢ Iris.inv N iprop(∃ v : Nat, l ↦ v ∗ ⌜0 < v⌝) -∗
      wpi_mask GF Hd m (AtomicHeapAPI.cas (E := E) (T := Nat) l old new)
        (fun _ => iprop(True)) ⊤ := by
  iintro #Hinv
  istep
  iinv_atomic Hinv with ⟨⟨%v, Hl, %hv⟩, Hcl⟩ back Hback
  iexists v
  isplitl [Hl]
  · iexact Hl
  · imodintro
    iintro %_y Hl'
    imod Hback
    ihave HI : iprop(∃ w : Nat, l ↦ w ∗ ⌜0 < w⌝) $$ [Hl']
    · by_cases hc : v = old
      · simp only [hc, if_pos]
        iexists new
        isplitl [Hl']
        · iexact Hl'
        · ipureintro; exact hnew
      · simp only [hc, if_false]
        iexists v
        isplitl [Hl']
        · iexact Hl'
        · ipureintro; exact hv
    ispecialize Hcl $$ HI
    imod Hcl
    imodintro
    iintro %_z _
    itrivial

end Examples

end AeneasIris.Tests.AtomicHeapAPI
