import AeneasIris.Tactics.Core

/-! # A zoo of divergence, and what each judgment says about it Five programs, three judgments. -/

namespace AeneasIris.Tests.Zoo

open Iris BI Aeneas.Data.Coinductive
open AeneasIris AeneasIris.HeapAPI AeneasIris.Heap
open scoped AeneasIris
open AeneasIris.Rust (rustH)
open Aeneas.Std (Result RustEffect Loc Error)
open Aeneas.Std.WP (spec dspec)

unseal Aeneas.Std.Result

section

variable {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF] [HeapGS.{0} GF]

abbrev RH (GF : BundledGFunctors) [Iris.InvGS_gen hlc GF] [HeapGS.{0} GF] :
    Handler RustEffect GF := rustH .part

/-! ## A. -/

def returns : Result Nat := Result.ok 42

example : spec returns (fun n => n = 42) := .ret _ _ rfl
example : dspec returns (fun n => n = 42) := .ret _ _ rfl

example (M : CoPset) :
    (emp : IProp GF) ⊢ WP returns @ (RH GF, Mode.part) ; M ⦃ n, ⌜n = 42⌝ ⦄ := by
  iintro -
  unfold returns
  iret
  ipureintro; rfl

/-! ## B. -/

def silent : Result Nat := silent
partial_fixpoint

/-- Not provable, and that is a theorem: `spec_div` is an `↔`. -/
example (p : Nat → Prop) : spec (Aeneas.Std.Result.div (α := Nat)) p ↔ False :=
  Aeneas.Std.WP.spec_div

/-- Provable, for *any* postcondition — this is what partial correctness buys. -/
example (p : Nat → Prop) : dspec (Aeneas.Std.Result.div (α := Nat)) p := .div p

/-- `wpi` sides with `spec`, not with `dspec`: the weakest precondition of `div` is `False` (under a mask chang… -/
example (Φ : Post GF Nat) :
    wpi GF (RH GF) .part (ITree.div) Φ ⊣⊢ iprop(|={∅}=> True) :=
  wpi_div_emp (H := RH GF) (m := .part) Φ

/-- The same `div`, read at `.total`: divergence is a failure. -/
example (Φ : Post GF Nat) :
    wpi GF (rustH (GF := GF) .total) .total (ITree.div) Φ ⊣⊢ iprop(|={∅}=> False) :=
  wpi_div_emp (H := rustH .total) (m := .total) Φ

/-- And so a diverging tree is provable at `.partial` outright. -/
example (Φ : Post GF Nat) : ⊢ wpi GF (RH GF) .part (ITree.div) Φ := by
  refine .trans ?_ (wpi_div_emp (H := RH GF) (m := .part) Φ).2
  simp only [divOK_partial]
  exact BI.true_intro.trans Iris.fupd_intro

/-! ## C. -/

noncomputable def effectful (l : Loc) : Result Nat := do
  let v ← load (T := Nat) l
  if v = 0 then effectful l else Result.ok v
partial_fixpoint

example (l : Loc) (v : Nat) (M : CoPset) :
    (iprop(l ↦ v) : IProp GF) ⊢
      WP (effectful l) @ (RH GF, Mode.part) ; M ⦃ r, ⌜r ≠ 0⌝ ∗ l ↦ v ⦄ := by
  iintro Hl
  iloeb as IH
  iunfold effectful
  istep
  by_cases h : v = 0
  ·
    simp only [h, if_pos]
    iapply IH $$ Hl
  · simp only [if_neg h]
    iret
    isplitr [Hl]
    · ipureintro; exact h
    · iexact Hl

/-! ## D. -/

noncomputable def effectfulOk (l : Loc) : Result Nat := do
  let _ ← store l (7 : Nat)
  load (T := Nat) l

example (l : Loc) (v : Nat) (M : CoPset) :
    (iprop(l ↦ v) : IProp GF) ⊢
      WP (effectfulOk l) @ (RH GF, Mode.part) ; M ⦃ r, ⌜r = 7⌝ ∗ l ↦ (7 : Nat) ⦄ := by
  iintro Hl
  iunfold effectfulOk
  istep
  istep
  isplitr [Hl]
  · itrivial
  · iexact Hl

/-! ## E. -/

def panics : Result Nat := Fail.fail .panic

/-- The precondition needed to reach a panic is `False`. -/
example (Φ : Post GF Nat) (M : CoPset) :
    iprop(|={M, ∅}=> False) ⊢ wpi_mask GF (RH GF) .part panics Φ M :=
  Fail.wpi_fail (Hd := RH GF) .panic Φ M

end

end AeneasIris.Tests.Zoo
