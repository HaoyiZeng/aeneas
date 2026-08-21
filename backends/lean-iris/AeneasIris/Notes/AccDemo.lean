import AeneasIris.Notes.AccLib

namespace AccDemo
open Iris BI Aeneas.Data.Coinductive
open AeneasIris AeneasIris.Heap AeneasIris.HeapAPI AeneasIris.AtomicHeapAPI
open Aeneas.Std (StateE StepE Loc Val RustHeap)
open scoped Aeneas.Std
open scoped AeneasIris.OneShotWpi
open AccLib

variable {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF] [G : HeapGS.{0} GF]
variable {E : Effect.{1}} [StateE RustHeap.{0} -< E] [StepE.{1} -< E]
variable [Aeneas.Std.ConcE.{1} -< E] [Aeneas.Std.FailE.{1} -< E]
variable {Hd : Handler E GF} [stateH heapInterp.{0} -<ₕ Hd] [Conc.ConcH GF -<ₕ Hd]
variable {m : Mode} [AeneasIris.Step.stepH GF m -<ₕ Hd]

/-! Four operations, one shared invariant, one tactic.  The client never sees a
closer, a mask or the invariant body; each `·` is an obligation, not plumbing. -/

section Shared
variable (l : Loc) (N : Namespace)

/-- `load` — read-only, so the accessor needs no obligation at all. -/
example : ⊢ Iris.inv N iprop(∃ v : Nat, l ↦ v ∗ ⌜0 < v⌝) -∗
    wpi_mask GF Hd m (AtomicHeapAPI.load (E := E) (T := Nat) l)
      (fun r => iprop(⌜0 < r⌝)) ⊤ := by
  iintro #Hinv
  istep
  iacc Hinv with Acc.cellInv_ro
  · intro x y; iintro %hx; iintro %z _; ipureintro; exact hx

/-- `store` — writes a constant, so the obligation is that the constant is good. -/
example (w : Nat) (hw : 0 < w) : ⊢ Iris.inv N iprop(∃ v : Nat, l ↦ v ∗ ⌜0 < v⌝) -∗
    wpi_mask GF Hd m (AtomicHeapAPI.store (E := E) l w)
      (fun _ => iprop(True)) ⊤ := by
  iintro #Hinv
  istep
  iacc Hinv with Acc.cellInv _
  · exact fun v _ _ => cell_keep l _ w hw
  · intro x y; iintro _; iintro %z _; itrivial

/-- `faa` — the value written back depends on the value read. -/
example (n : Nat) : ⊢ Iris.inv N iprop(∃ v : Nat, l ↦ v ∗ ⌜0 < v⌝) -∗
    wpi_mask GF Hd m (AtomicHeapAPI.faa (E := E) (T := Nat) l n)
      (fun r => iprop(⌜0 < r⌝)) ⊤ := by
  iintro #Hinv
  istep
  iacc Hinv with Acc.cellInv ?_
  · exact fun v _ h => cell_keep l _ (v + n) (Nat.lt_of_lt_of_le h (Nat.le_add_right v n))
  · intro x y; iintro %hx; iintro %z _; ipureintro; exact hx

/-- `cas` — the dependency is a case split, which is exactly the obligation. -/
example (old new : Nat) (hnew : 0 < new) : ⊢ Iris.inv N iprop(∃ v : Nat, l ↦ v ∗ ⌜0 < v⌝) -∗
    wpi_mask GF Hd m (AtomicHeapAPI.cas (E := E) (T := Nat) l old new)
      (fun _ => iprop(True)) ⊤ := by
  iintro #Hinv
  istep
  iacc Hinv with Acc.cellInv ?_
  · intro v y h
    by_cases hc : v = old
    · simp only [hc, if_pos]; exact cell_keep l _ new hnew
    · simp only [hc, if_false]; exact cell_keep l _ v h
  · intro x y; iintro _; iintro %z _; itrivial

end Shared

end AccDemo
