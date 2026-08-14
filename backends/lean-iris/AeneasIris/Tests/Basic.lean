import AeneasIris.Tactics.Core

/-! # Tests The two things this development has to do at once, on one goal: * replay Aeneas' `⦃⦄` lemmas on pur… -/

namespace AeneasIris.Tests.Basic

open Iris BI Aeneas.Data.Coinductive
open AeneasIris AeneasIris.HeapAPI AeneasIris.Heap
open scoped AeneasIris
open scoped Aeneas
open AeneasIris.Rust (rustH iSpec_total_to_partial wpi_total_to_partial)
open Aeneas.Std (Result RustEffect Loc Slice U32 Usize)
open Aeneas.Std.alloc.vec (Vec)

unseal Aeneas.Std.Result

section

variable {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF] [HeapGS.{0} GF]

/-- The handler these tests run under: partial correctness, so that every operation issues a `▷` and Löb induct… -/
abbrev RH (GF : BundledGFunctors) [Iris.InvGS_gen hlc GF] [HeapGS.{0} GF] :
    Handler RustEffect GF := rustH .part

/-- A stand-in for a translated Rust function, with an Aeneas-style spec. -/
def twice (n : Nat) : Result Nat := .ok (2 * n)

@[step]
theorem twice_spec (n : Nat) : Aeneas.Std.WP.spec (twice n) (fun r => r = 2 * n) :=
  .ret _ _ rfl

/-! ## Pure calls -/

/-- The lifting on its own. -/
example (n : Nat) (H : Handler RustEffect GF) (m : Mode) (P : IProp GF) (M : CoPset) :
    iSpec H m P (twice n) (fun v => iprop(⌜v = 2 * n⌝ ∧ P)) M :=
  spec_to_iSpec (twice_spec n)

/-- Two calls in a row, sequenced with `do`, from the empty precondition. -/
example (n : Nat) (H : Handler RustEffect GF) (m : Mode) (M : CoPset) :
    ⊢ WP (do let a ← twice n; twice a : Result Nat) @ (H, m) ; M ⦃ v, (⌜v = 4 * n⌝ : IProp GF) ⦄ := by
  iintro
  istep
  istep
  ipureintro
  simp [*]; ring

/-- The same, with a non-trivial precondition, which must come out untouched. -/
example (n : Nat) (H : Handler RustEffect GF) (m : Mode) (R : IProp GF) (M : CoPset) :
    R ⊢ WP (do let a ← twice n; twice a : Result Nat) @ (H, m) ; M ⦃ v, ⌜v = 4 * n⌝ ∧ R ⦄ := by
  istep
  istep
  iintro HR
  isplit
  · ipureintro; simp [*]; ring
  · iexact HR

/-! ## Heap operations -/

example (l : Loc) (M : CoPset) :
    (iprop(l ↦ (1 : Nat)) : IProp GF) ⊢
      WP (do let _ ← store (E := RustEffect) l (2 : Nat)
             load (T := Nat) l : Result Nat) @ (RH GF, Mode.part) ; M ⦃ v, ⌜v = 2⌝ ⦄ := by
  iintro Hl
  istep
  istep
  itrivial

/-! ## The point: both kinds of step, with a frame A pure Aeneas call, a heap write, another pure call, a heap… -/

example (l : Loc) (n : Nat) (R : IProp GF) (M : CoPset) :
    iprop(l ↦ (0 : Nat) ∗ R) ⊢
      WP (do let a ← twice n
             let _ ← store (E := RustEffect) l a
             let _b ← twice a
             load (T := Nat) l : Result Nat) @ (RH GF, Mode.part) ; M ⦃ v, ⌜v = 2 * n⌝ ∗ R ⦄ := by
  iintro ⟨Hl, HR⟩
  istep as ⟨a, ha⟩
  istep
  istep as ⟨b, hb⟩
  istep
  isplitr [HR]
  · ipureintro; simp [*]
  · iexact HR

/-! ## A real Aeneas function, verified through `iSpec` Nothing above uses a genuine standard-library lemma — `… -/

/-- Read two cells of a slice, add them, and write the sum back to the first — the shape of a translated Rust f… -/
def addInto (s : Slice U32) (i j : Usize) : Result (Slice U32) := do
  let a ← s.index_usize i
  let b ← s.index_usize j
  let c ← a + b
  s.update i c

theorem addInto_spec (s : Slice U32) (i j : Usize)
    (hi : i.val < s.length) (hj : j.val < s.length)
    (hmax : (s.val[i.val]!).val + (s.val[j.val]!).val ≤ U32.max) :
    addInto s i j ⦃ ns => ns.val.length = s.val.length ⦄ := by
  unfold addInto
  step as ⟨a, ha⟩
  step as ⟨b, hb⟩
  step as ⟨c, hc⟩
  · simp_lists [*] at *; scalar_tac
  step as ⟨ns, hns⟩
  simp [*]

example (s : Slice U32) (i j : Usize) (R : IProp GF) (M : CoPset)
    (hi : i.val < s.length) (hj : j.val < s.length)
    (hmax : (s.val[i.val]!).val + (s.val[j.val]!).val ≤ U32.max) :
    R -∗ WP (addInto s i j) @ (RH GF, Mode.part) ; M ⦃ ns, ⌜ns.val.length = s.val.length⌝ ∗ R ⦄ := by
  iintro HR
  unfold addInto
  istep as ⟨a, ha⟩
  istep as ⟨b, hb⟩
  istep as ⟨c, hc⟩
  · simp_lists [*] at *; scalar_tac
  istep as ⟨ns, hns⟩
  isplitr [HR]
  · ipureintro; simp [*]
  · iexact HR

/-! ## A longer function, and a cell to put its answer in `pushSum` is six library calls: two indexings, an add… -/

/-- Add the first two elements of a vector and append the sum. -/
def pushSum (v : Vec U32) : Result (Vec U32 × U32) := do
  let a ← v.index_usize 0#usize
  let b ← v.index_usize 1#usize
  let c ← a + b
  let v1 ← v.push c
  Result.ok (v1, c)

@[step]
theorem pushSum_spec (v : Vec U32) (h0 : 0 < v.val.length) (h1 : 1 < v.val.length)
    (hlen : v.val.length < Usize.max)
    (hmax : (v.val[0]!).val + (v.val[1]!).val ≤ U32.max) :
    pushSum v ⦃ (_nv, c) => c.val = (v.val[0]!).val + (v.val[1]!).val ⦄ := by
  unfold pushSum
  step as ⟨a, ha⟩
  step as ⟨b, hb⟩
  step as ⟨c, hc⟩
  · simp_lists [*] at *; scalar_tac
  step as ⟨v1, hv1⟩
  simp_lists [*] at *

/-- Allocate a cell holding `0`, run `pushSum`, write its answer into the cell, and read it back. -/
noncomputable def cellDemo (v : Vec U32) : Result (Loc × U32) := do
  let l ← HeapAPI.alloc (0#u32)
  let (_, c) ← pushSum v
  let _ ← store l c
  let r ← load (T := U32) l
  Result.ok (l, r)

/-- The whole thing: the value read back is the sum, and the caller is handed the cell that holds it. -/
example (v : Vec U32) (M : CoPset)
    (h0 : 0 < v.val.length) (h1 : 1 < v.val.length)
    (hlen : v.val.length < Usize.max)
    (hmax : (v.val[0]!).val + (v.val[1]!).val ≤ U32.max) :
    (emp : IProp GF) ⊢ WP (cellDemo v) @ (RH GF, Mode.part) ; M
      ⦃ lr, ⌜(lr.2).val = (v.val[0]!).val + (v.val[1]!).val⌝ ∗ lr.1 ↦ lr.2 ⦄ := by
  iintro -
  iunfold cellDemo
  istep as ⟨l, Hl⟩
  istep as ⟨⟨_, c⟩, hp⟩
  istep
  istep
  istep
  isplitr
  · itrivial
  · itrivial

/-! ## Recursion: a spin loop, closed by Löb induction This is the shape every unbounded wait has, and the shap… -/

noncomputable def spin (l : Loc) : Result Nat := do
  let v ← load (T := Nat) l
  if v = 0 then spin l else Result.ok v
partial_fixpoint

theorem spin_spec (l : Loc) (v : Nat) (M : CoPset) :
    (iprop(l ↦ v) : IProp GF) ⊢ WP (spin l) @ (RH GF, Mode.part) ; M ⦃ r, ⌜r ≠ 0⌝ ∗ l ↦ v ⦄ := by
  iintro Hl
  iloeb as IH
  iunfold spin
  istep
  by_cases h : v = 0
  · simp only [h, if_pos]
    iapply IH $$ Hl
  · simp only [if_neg h]
    istep
    isplitr [Hl]
    · ipureintro; exact h
    · iexact Hl

/-! ## Registering a spec of one's own The point of the triple notation: a composite operation gets a spec in e… -/

noncomputable def bump (l : Loc) : Result Nat := do
  let v ← load (T := Nat) l
  let _ ← store l (v + 1)
  Result.ok v

@[istep_rule]
theorem bump_spec (l : Loc) (v : Nat) (M : CoPset) :
    ⦃ l ↦ v ⦄ (bump l) @ (RH GF) ; Mode.part ; M ⦃ r, ⌜r = v⌝ ∗ l ↦ (v + 1) ⦄ := by
  iintro Hl
  iunfold bump
  istep
  istep
  istep
  isplitr
  · itrivial
  · itrivial

/-- And now it is just another step — twice, with a frame the spec never mentions and `istep` never names. -/
example (l k : Loc) (M : CoPset) :
    (iprop(l ↦ (3 : Nat) ∗ k ↦ (7 : Nat)) : IProp GF)
      ⊢ WP (do let a ← bump l; let b ← bump l; Result.ok (a + b)) @ (RH GF, Mode.part) ; M
        ⦃ r, ⌜r = 7⌝ ∗ l ↦ (5 : Nat) ∗ k ↦ (7 : Nat) ⦄ := by
  iintro ⟨Hl, Hk⟩
  istep
  istep
  istep
  isplitr
  · itrivial
  · isplitl [Hl]
    · itrivial
    · itrivial

/-! ## The `Mode` knob Four things to check: that `.total` really is a stronger reading, that a proof written a… -/

/-- The handler at total correctness. Same language, `stepH` at the other mode. -/
abbrev TH (GF : BundledGFunctors) [Iris.InvGS_gen hlc GF] [HeapGS.{0} GF] :
    Handler RustEffect GF := rustH .total

/-- The knob is visible on `div` and nowhere else: at `.partial` divergence is granted outright. -/
example (Φ : Post GF Nat) : ⊢ wpi GF (RH GF) .part ITree.div Φ := by
  refine .trans ?_ (wpi_div_emp (H := RH GF) (m := .part) Φ).2
  simp only [divOK_partial]
  exact BI.true_intro.trans Iris.fupd_intro

/-- At `.total` the same tree's weakest precondition is `|={∅}=> False` — not merely unproven but unprovable, w… -/
example (Φ : Post GF Nat) :
    wpi GF (TH GF) .total ITree.div Φ ⊣⊢ iprop(|={∅}=> False) := by
  simpa only [divOK_total] using wpi_div_emp (H := TH GF) (m := .total) Φ

/-- A heap program, proved at `.total`. -/
noncomputable def bumpCell (l : Loc) : Result U32 := do
  let x ← load (T := U32) l
  let _ ← store l (x.wrapping_add 1#u32)
  load (T := U32) l

theorem bump_spec_total (l : Loc) (v : U32) (M : CoPset) :
    ⦃ l ↦ v ⦄ (bumpCell l) @ (TH GF) ; Mode.total ; M ⦃ r, ⌜r = v.wrapping_add 1#u32⌝ ∗ l ↦ r ⦄ := by
  iintro Hl
  iunfold bumpCell
  istep as ⟨x, Hl⟩
  istep as ⟨_, Hl⟩
  istep as ⟨r, Hl⟩
  isplitr
  · ipureintro; simp_all
  · iexact Hl

/-- And the same statement at `.partial`, for free. -/
theorem bump_spec_partial (l : Loc) (v : U32) (M : CoPset) :
    ⦃ l ↦ v ⦄ (bumpCell l) @ (RH GF) ; Mode.part ; M ⦃ r, ⌜r = v.wrapping_add 1#u32⌝ ∗ l ↦ r ⦄ :=
  iSpec_total_to_partial (bump_spec_total (GF := GF) l v M)

/-- The transport is available on bare weakest preconditions too, so it composes with anything, not only with t… -/
example (l : Loc) (v : U32) (M : CoPset) :
    (iprop(l ↦ v) : IProp GF) ⊢ WP (bumpCell l) @ (RH GF, Mode.part) ; M
      ⦃ r, ⌜r = v.wrapping_add 1#u32⌝ ∗ l ↦ r ⦄ :=
  (bump_spec_total (GF := GF) l v M).trans (wpi_total_to_partial _ _ M)

/-! ### One parameter, not two The mode reaches `wpi` by two routes — the `▷` that `stepH` mints on the `vis` b… -/

/-- Both readings of a single `m`, side by side. -/
example (m : Mode) (Φ : Post GF Nat) :
    wpi GF (rustH (GF := GF) m) m ITree.div Φ ⊣⊢ iprop(|={∅}=> divOK GF m) :=
  wpi_div_emp (H := rustH m) (m := m) Φ

/-- Mode-polymorphic specs are the norm, not a special case: a spec that names no mode holds at both, and its `… -/
example (m : Mode) (Hd : Handler RustEffect GF)
    [AeneasIris.Step.stepH.{1} GF m -<ₕ Hd] (P : IProp GF) (M : CoPset) :
    ⦃ Step.lat m P ⦄ (Step.stepP.{0, 1} (E := RustEffect)) @ Hd ; m ; M ⦃ _r, P ⦄ :=
  AeneasIris.step_spec (E := RustEffect) (Hd := Hd) (m := m) P M

/-- Instantiating that one variable moves both routes at once: the precondition loses its `lat`, because `lat .… -/
example (Hd : Handler RustEffect GF)
    [AeneasIris.Step.stepH.{1} GF .total -<ₕ Hd] (P : IProp GF) (M : CoPset) :
    ⦃ P ⦄ (Step.stepP.{0, 1} (E := RustEffect)) @ Hd ; Mode.total ; M ⦃ _r, P ⦄ :=
  AeneasIris.step_spec (E := RustEffect) (Hd := Hd) (m := .total) P M

end

end AeneasIris.Tests.Basic
