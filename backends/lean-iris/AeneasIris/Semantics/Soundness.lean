import AeneasIris.Semantics.Preservation
import Iris.Instances.Lib.WSat
import Iris.Instances.Lib.LaterCredits
import Iris.Instances.Lib.Invariants
import Iris.Instances.Lib.GhostMap
import Iris.Std.HeapInstances

/-!
# Soundness: from the system invariant to the two closed statements

This file is the plumbing that turns the four preservation lemmas of
`Semantics/Preservation.lean` into the pure-Lean facts `Safe t` and
`MayReturn t v → φ v`. It contains no reasoning about handlers at all;
everything specific to `rustH` already happened in `Preservation.lean`.

There are exactly three moving parts.

**1. `n`-step preservation.** `sysInv_reachesN` iterates `sysInv_step` along a
`ReachesN` derivation, paying one `|={∅}▷=>` per machine step. Fixing the step
count *before* entering the logic is why `Machine.lean` provides `ReachesN` and
`Reaches.toReachesN` alongside `Reaches`: the `n` of `|={∅}▷=>^[n]` has to be a
Lean-level natural, and `Reaches` does not carry one.

**2. A concrete model.** `ProvableSpec` quantifies over every
`BundledGFunctors`, so the soundness proof gets to choose one. `SoundGF` is
iris-lean's `Examples/ClosedProofs.GF` — the invariant map, the two
mask-bookkeeping slots, later credits — plus **one extra slot** for the heap,
at the functor `GhostMapG` unfolds to. Slot 4 is the only difference from that
template, and it is what lets this file allocate the heap ghost state itself,
so the client never has to.

**3. `hlc := .hasNoLC`.** Both final steps deliver the postcondition at a mask
that is not the ambient one: `sysInv_not_faulty` ends in `|={∅}=> ⌜…⌝` and
`sysInv_return` in `|={∅,⊤}=> ⌜…⌝`. Since `⌜·⌝` is `Plain`, `fupd_plain_mask`
collapses the mask change — but iris-lean only provides the `BIFUpdatePlainly`
instance at `.hasNoLC`, later credits and fupd-plainly being incompatible. This
is the sole reason `ProvableSpec` quantifies over `hlc`. No later credits are
needed: `step_fupdN_soundness` is invoked at `m := 0`, and the `▷`s are supplied
by the `▷` slot of `|={∅}▷=>^[n]`.

Both closed results run `step_fupdN_soundness` at `n + 1` rather than `n`. The
extra step is free (`step_fupdN_le`) and is what makes `step_fupdN_S_fupd`
applicable, which is how the trailing `|={∅}=>` gets absorbed; at `n = 0` there
would be no `▷` to absorb it into.

## Why `ProvableSpec` is spelled out here

`ProvableSpec` is defined in `Semantics/Adequacy.lean`, which is *downstream* of
this file — it is where the two final theorems live, and they are proved by the
results below. So the hypothesis is restated here as `ProvableSpecOf`, an
`abbrev` that is definitionally the same `∀ GF hlc, …`; `Adequacy.lean` can
therefore pass its `ProvableSpec .part t φ` straight in.
-/

namespace AeneasIris.Semantics

open Iris BI COFE HeapView Auth Aeneas.Data.Coinductive
open AeneasIris.Heap (HeapGS heapInterp)
open Aeneas.Std (Result RustEffect RustHeap Loc Cell Val HMap)

unseal Aeneas.Std.Result

/-! ## n-step preservation -/

/-- **`sysInv_step`, iterated.** `n` machine steps cost `n` `|={∅}▷=>`s.

This is the only place the step count is used, and it is why `Machine.lean`
carries `ReachesN` at all: `step_fupdN_soundness` needs `n` as a Lean natural,
fixed before entering the logic. -/
theorem sysInv_reachesN {hlc : Iris.HasLC} {GF : BundledGFunctors}
    [Iris.InvGS_gen hlc GF] [HeapGS.{0} GF] {α : Type} (m : Mode) (Φ : α → IProp GF)
    {n : Nat} {c c' : Config α} (h : ReachesN n c c') :
    SysInv m Φ c ⊢ iprop(|={∅}▷=>^[n] SysInv m Φ c') := by
  induction h with
  | refl c => exact .rfl
  | tail hs _ ih =>
    simp only [Nat.repeat]
    exact (sysInv_step m Φ hs).trans (step_fupd_mono ih)

/-! ## A concrete Iris model, with a heap slot

`GhostMapG GF K V H` unfolds to
`ElemG GF (constOF (HeapView K (Agree (LeibnizO V)) H))`, so the extra slot is
that functor at `K := Loc`, `V := Cell Val.{0}`, `H := HMap` — exactly what
`AeneasIris.Heap.HeapGS` asks for. Note `Val.{0} : Type 1`, so this slot sits a
universe above every slot of the iris-lean template; the universe parameters of
`BundledGFunctors` absorb that, and `IProp SoundGF` follows it up. -/
noncomputable def SoundGF : BundledGFunctors := fun n =>
  match n with
  | 0 => ⟨InvMapF, by infer_instance⟩
  | 1 => ⟨constOF (ULift CoPsetDisjL), by infer_instance⟩
  | 2 => ⟨constOF (ULift (DisjointLeibnizSet PosSet)), by infer_instance⟩
  | 3 => ⟨AuthURF (constOF (ULift Credit)), by infer_instance⟩
  | 4 => ⟨constOF (HeapView Loc (Agree (LeibnizO (Cell Val.{0}))) HMap), by infer_instance⟩
  | _ => ⟨constOF (ULift Unit), by infer_instance⟩

instance : WsatGpreS SoundGF where
  inv := { τ := 0, transp := by unfold SoundGF; rfl }
  enabled := { τ := 1, transp := by unfold SoundGF; rfl }
  disabled := { τ := 2, transp := by unfold SoundGF; rfl }

instance : LcGpreS SoundGF where
  lc_elem := { τ := 3, transp := by unfold SoundGF; rfl }

instance : InvGpreS SoundGF where
  toWsatGpreS := inferInstance
  toLcGpreS := inferInstance

/-- The heap slot, as the `GhostMapG` that `HeapGS` wraps. -/
instance soundGhostMapG : GhostMapG SoundGF Loc (Cell Val.{0}) HMap where
  elem := { τ := 4, transp := by unfold SoundGF; rfl }

/-- `HeapGS` is that `GhostMapG` plus a ghost name, and the name is exactly what
`ghost_map_alloc` hands back. -/
abbrev soundHeapGS (γ : GName) : HeapGS.{0} SoundGF := ⟨soundGhostMapG, γ⟩

/-! ## The hypothesis

Definitionally `Adequacy.ProvableSpec`, restated here because `Adequacy.lean` is
downstream. -/

/-- See `Semantics/Adequacy.lean`'s `ProvableSpec`, of which this is the
definitional unfolding. -/
abbrev ProvableSpecOf (m : Mode) {α : Type} (t : Result α) (φ : α → Prop) : Prop :=
  ∀ (GF : BundledGFunctors) (hlc : Iris.HasLC) [Iris.InvGS_gen hlc GF] [HeapGS.{0} GF],
    ⦃ emp ⦄ t @ (Rust.rustH (GF := GF) m) ; m ; ⊤ ⦃ v, ⌜φ v⌝ ⦄

/-! ## The common core -/

/-- From the freshly allocated empty-heap authority to the system invariant at
the reached configuration, `n` `▷`s later.

`heapInterp` at the `HeapGS` built from `γ` is *definitionally*
`ghost_map_auth γ (.own 1) ·`, which is what lets the callers below feed
`ghost_map_alloc`'s output straight in. -/
theorem sysInv_of_provable {α : Type} {t : Result α} {φ : α → Prop}
    (h : ProvableSpecOf .part t φ) {n : Nat} {c : Config α}
    (hn : ReachesN n (init t) c)
    [Iris.InvGS_gen .hasNoLC SoundGF] [HeapGS.{0} SoundGF] :
    iprop(heapInterp (∅ : RustHeap.{0}))
      ⊢ iprop(|={⊤,∅}=> |={∅}▷=>^[n]
          SysInv (GF := SoundGF) .part (fun v => iprop(⌜φ v⌝)) c) := by
  have hwp := h SoundGF .hasNoLC
  refine .trans (sep_emp (PROP := IProp SoundGF)).2 ?_
  refine .trans (sep_mono_right hwp) ?_
  refine .trans (sysInv_init .part (fun v => iprop(⌜φ v⌝)) t) ?_
  exact BIFUpdate.mono (sysInv_reachesN .part _ hn)

/-! ## The two closed results

Both have the same shape: fix the step count outside the logic, enter it with
`pure_soundness` + `step_fupdN_soundness` at `.hasNoLC`, allocate the heap,
run `sysInv_of_provable`, and read off the conclusion with the relevant
preservation lemma. -/

/-- **Partial correctness, safety half.** No reachable configuration is about to
panic or to perform an undefined heap operation. -/
theorem safe_of_provable {α : Type} {t : Result α} {φ : α → Prop}
    (h : ProvableSpecOf .part t φ) : Safe t := by
  intro c hr
  obtain ⟨n, hn⟩ := hr.toReachesN
  refine pure_soundness (PROP := IProp SoundGF) ?_
  refine step_fupdN_soundness (GF := SoundGF) (hlc := .hasNoLC) (n := n + 1) (m := 0) ?_
  intro Hinv
  have final : ∀ γ : GName,
      (Iris.ghost_map_auth (GF := SoundGF) (H := HMap) γ (DFrac.own 1)
          (∅ : HMap (Cell Val.{0})))
        ⊢ iprop(|={⊤,∅}=> |={∅}▷=>^[n + 1] ⌜¬ c.Faulty⌝) := by
    intro γ
    letI HG : HeapGS.{0} SoundGF := soundHeapGS γ
    show iprop(heapInterp (∅ : RustHeap.{0})) ⊢ _
    refine .trans (sysInv_of_provable h hn) (BIFUpdate.mono ?_)
    refine .trans (step_fupdN_mono (sysInv_not_faulty .part _ c)) ?_
    refine .trans (step_fupdN_le (Nat.le_succ n) (subset_refl ..)) ?_
    exact step_fupdN_S_fupd.mpr
  iintro _
  imod (Iris.ghost_map_alloc (GF := SoundGF) (K := Loc) (V := Cell Val.{0}) (H := HMap)
        (∅ : HMap (Cell Val.{0}))) with ⟨%γ, Hauth, -⟩
  iapply (BI.entails_wand (final γ))
  iexact Hauth

/-- **Partial correctness, postcondition half.** If the main thread is scheduled
and has returned `v`, then `φ v`. -/
theorem post_of_provable {α : Type} {t : Result α} {φ : α → Prop}
    (h : ProvableSpecOf .part t φ) : ∀ v, MayReturn t v → φ v := by
  rintro v ⟨c, hr, hcur, hfoc⟩
  obtain ⟨n, hn⟩ := hr.toReachesN
  refine pure_soundness (PROP := IProp SoundGF) ?_
  refine step_fupdN_soundness (GF := SoundGF) (hlc := .hasNoLC) (n := n + 1) (m := 0) ?_
  intro Hinv
  have final : ∀ γ : GName,
      (Iris.ghost_map_auth (GF := SoundGF) (H := HMap) γ (DFrac.own 1)
          (∅ : HMap (Cell Val.{0})))
        ⊢ iprop(|={⊤,∅}=> |={∅}▷=>^[n + 1] ⌜φ v⌝) := by
    intro γ
    letI HG : HeapGS.{0} SoundGF := soundHeapGS γ
    show iprop(heapInterp (∅ : RustHeap.{0})) ⊢ _
    refine .trans (sysInv_of_provable h hn) (BIFUpdate.mono ?_)
    -- `sysInv_return` hands the big lock back, hence lands at `|={∅,⊤}=>`;
    -- `⌜φ v⌝` is `Plain`, so `fupd_plain_mask` closes the mask again.
    refine .trans (step_fupdN_mono
      ((sysInv_return .part _ hcur hfoc).trans fupd_plain_mask)) ?_
    refine .trans (step_fupdN_le (Nat.le_succ n) (subset_refl ..)) ?_
    exact step_fupdN_S_fupd.mpr
  iintro _
  imod (Iris.ghost_map_alloc (GF := SoundGF) (K := Loc) (V := Cell Val.{0}) (H := HMap)
        (∅ : HMap (Cell Val.{0}))) with ⟨%γ, Hauth, -⟩
  iapply (BI.entails_wand (final γ))
  iexact Hauth

end AeneasIris.Semantics
