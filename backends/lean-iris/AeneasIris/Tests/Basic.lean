import AeneasIris.Tactics

/-!
# Tests

The two things this development has to do at once, on one goal:

* replay Aeneas' `⦃⦄` lemmas on pure calls, without restating them, and
* apply the handler rules to operations that touch the heap,

with a frame that neither of them disturbs.

The handler is `rustH .later` throughout: the modality has to be concrete for
`lat` to reduce, and `.later` is the one that makes Löb induction available.
-/

namespace AeneasIris.Test

open Iris BI Aeneas.Data.Coinductive
open AeneasIris AeneasIris.HeapAPI AeneasIris.Heap
open scoped AeneasIris
open scoped Aeneas
open AeneasIris.RustHandler (rustH)
open Aeneas.Std (Result RustEffect Loc Slice U32 Usize)
open Aeneas.Std.alloc.vec (Vec)

unseal Aeneas.Std.Result

section

variable {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF] [HeapGS.{0} GF]

/-- The handler these tests run under: partial correctness, so that every
operation issues a `▷` and Löb induction is available. -/
abbrev RH (GF : BundledGFunctors) [Iris.InvGS_gen hlc GF] [HeapGS.{0} GF] :
    Handler RustEffect GF := rustH .later



/-- A stand-in for a translated Rust function, with an Aeneas-style spec. -/
def twice (n : Nat) : Result Nat := .ok (2 * n)

@[step]
theorem twice_spec (n : Nat) : Aeneas.Std.WP.spec (twice n) (fun r => r = 2 * n) :=
  .ret _ _ rfl

/-! ## Pure calls -/

/-- The lifting on its own. -/
example (n : Nat) (H : Handler RustEffect GF) (P : IProp GF) (M : CoPset) :
    iSpec H P (twice n) (fun v => iprop(⌜v = 2 * n⌝ ∧ P)) M :=
  spec_to_iSpec (twice_spec n)

/-- Two calls in a row, sequenced with `do`, from the empty precondition.

`step` recognises the `Bind.bind`, finds `twice_spec` in the `@[step]`
database, lifts it through `spec_to_iSpec` and applies `iSpec_bind'`. This is
the `EmpValid` shape — the goal `⊢ …` is *definitionally* `emp ⊢ …`, and the
one judgment covers it. -/
example (n : Nat) (H : Handler RustEffect GF) (M : CoPset) :
    ⊢ WP (do let a ← twice n; twice a : Result Nat) @ H ; M ⦃ v, (⌜v = 4 * n⌝ : IProp GF) ⦄ := by
  iintro
  istep
  istep
  ipureintro
  simp [*]; ring

/-- The same, with a non-trivial precondition, which must come out untouched. -/
example (n : Nat) (H : Handler RustEffect GF) (R : IProp GF) (M : CoPset) :
    R ⊢ WP (do let a ← twice n; twice a : Result Nat) @ H ; M ⦃ v, ⌜v = 4 * n⌝ ∧ R ⦄ := by
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
             load (T := Nat) l : Result Nat) @ (RH GF) ; M ⦃ v, ⌜v = 2⌝ ⦄ := by
  iintro Hl
  iheap (store (E := RustEffect) l (2 : Nat))
    with (wpi_store (E := RustEffect) (Hd := RH GF) (m := .later)
            l (1 : Nat) (2 : Nat)) using Hl
  iintro Hl
  imodintro
  iheap! (wpi_load (Hd := RH GF) (m := .later) l (2 : Nat) (DFrac.own 1)) using Hl
  iintro _
  imodintro
  itrivial

/-! ## The point: both kinds of step, with a frame

A pure Aeneas call, a heap write, another pure call, a heap read — and a frame
`R` that no step is allowed to disturb.

`istep` never sees the heap and `iheap` never sees the `@[step]` database. The
two automations do not know about each other, and neither of them threads `R`:
it simply stays in the proof-mode context, which is the whole reason the heap
rules are applied by hand rather than registered. -/

example (l : Loc) (n : Nat) (R : IProp GF) (M : CoPset) :
    iprop(l ↦ (0 : Nat) ∗ R) ⊢
      WP (do let a ← twice n
             let _ ← store (E := RustEffect) l a
             let b ← twice a
             load (T := Nat) l : Result Nat) @ (RH GF) ; M ⦃ v, ⌜v = 2 * n⌝ ∗ R ⦄ := by
  iintro ⟨Hl, HR⟩
  istep as ⟨a, ha⟩
  iheap (store (E := RustEffect) l a)
    with (wpi_store (E := RustEffect) (Hd := RH GF) (m := .later)
            l (0 : Nat) a) using Hl
  iintro Hl
  imodintro
  istep as ⟨b, hb⟩
  iheap! (wpi_load (Hd := RH GF) (m := .later) l a (DFrac.own 1)) using Hl
  iintro Hl
  imodintro
  isplitr [HR]
  · ipureintro; simp [*]
  · iexact HR

/-! ## A real Aeneas function, verified through `iSpec`

Nothing above uses a genuine standard-library lemma — `twice_spec` is a
stand-in. This one is the actual thing: `swap` is written the way Aeneas emits
code, and every step of its proof is a `⦃⦄` lemma from `Aeneas.Std`, found and
applied by `step` with no restatement.

Note the two arithmetic calls carry *preconditions* (`hbound`, `hmax`). `step`
raises them as side goals exactly as it does for its own judgment. -/

/-- Read two cells of a slice, add them, and write the sum back to the first —
the shape of a translated Rust function. -/
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
    R -∗ WP (addInto s i j) @ (RH GF) ; M ⦃ ns, ⌜ns.val.length = s.val.length⌝ ∗ R ⦄ := by
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

/-! ## A longer function, and a cell to put its answer in

`pushSum` is six library calls: two indexings, an addition, a `Vec.push`, and
the return. `cellDemo` allocates a cell holding `0`, runs it, writes the answer
into the cell and reads it back.

The two halves are automated by different things and neither knows about the
other: `istep` replays the five `⦃⦄` lemmas, the heap rules are applied by hand,
and the points-to that `alloc` produces survives the pure calls in between. -/

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
    pushSum v ⦃ (nv, c) => c.val = (v.val[0]!).val + (v.val[1]!).val ⦄ := by
  unfold pushSum
  step as ⟨a, ha⟩
  step as ⟨b, hb⟩
  step as ⟨c, hc⟩
  · simp_lists [*] at *; scalar_tac
  step as ⟨v1, hv1⟩
  simp_lists [*] at *

/-- Allocate a cell holding `0`, run `pushSum`, write its answer into the cell,
and read it back. -/
noncomputable def cellDemo (v : Vec U32) : Result (Loc × U32) := do
  let l ← HeapAPI.alloc (0#u32)
  let (_, c) ← pushSum v
  let _ ← store l c
  let r ← load (T := U32) l
  Result.ok (l, r)

/-- The whole thing: the value read back is the sum, and the caller is handed
the cell that holds it.

Nothing is assumed to start with — the points-to in the postcondition is one
`alloc` created. It then has to survive four pure library calls, which is the
part neither automation is aware of: `istep` does not know the heap exists, and
the heap rules do not know about the `@[step]` database. -/
example (v : Vec U32) (M : CoPset)
    (h0 : 0 < v.val.length) (h1 : 1 < v.val.length)
    (hlen : v.val.length < Usize.max)
    (hmax : (v.val[0]!).val + (v.val[1]!).val ≤ U32.max) :
    (emp : IProp GF) ⊢ WP (cellDemo v) @ (RH GF) ; M
      ⦃ lr, ⌜(lr.2).val = (v.val[0]!).val + (v.val[1]!).val⌝ ∗ lr.1 ↦ lr.2 ⦄ := by
  iintro _
  unfold cellDemo
  ibind (HeapAPI.alloc (E := RustEffect) (T := U32) _)
  iapply (wpi_alloc (Hd := RH GF) (m := .later) (T := U32) _)
  ilat
  inext
  iintro %l Hl
  imodintro
  istep as ⟨p, hp⟩
  iheap (store (E := RustEffect) l p.2)
    with (wpi_store (E := RustEffect) (Hd := RH GF) (m := .later) l (0#u32) p.2) using Hl
  iintro Hl
  imodintro
  iheap (HeapAPI.load (E := RustEffect) (T := U32) l)
    with (wpi_load (Hd := RH GF) (m := .later) l p.2 (DFrac.own 1)) using Hl
  iintro Hl
  imodintro
  iapply (wpi_ret_result (H := RH GF) (l, p.2) _ M)
  isplitr [Hl]
  · ipureintro; exact hp
  · iexact Hl

end

end AeneasIris.Test
