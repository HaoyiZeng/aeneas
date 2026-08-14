import AeneasIris.Rust
import AeneasIris.Semantics.Machine
import AeneasIris.Semantics.Soundness
import AeneasIris.Semantics.Termination

/-!
# The final theorem

## Status

`adequacy_part` is **fully proved**: no `sorry`, no axiom beyond `propext`,
`Classical.choice`, `Quot.sound`.

`adequacy_total` is **also fully proved**. Its first two conjuncts come from
`ProvableSpec.total_to_part` plus `adequacy_part`; of `Terminates`, the
`¬ Config.Diverging` half is `sysInv_not_diverging` and the `SN` half runs
through `Termination.lean`'s chain
`wpi_TPf → TPf_app → TPf_singleton → TPf_parked → pool_TPf → pool_TP →
sysInv_TP → sysInv_snInv → sysInv_sn`. No `sorry`, no `axiom`:

```
'adequacy_total' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## The two sides

* `ProvableSpec` is the *logic* side: what a verification engineer actually
  proves, namely one `wpi` triple, in an arbitrary Iris model.
* `Safe` / `MayReturn` / `Terminates` (in `Semantics/Machine.lean`) are the
  *operational* side: pure `Prop`s about the machine, with no Iris in them.

The final theorem is the bridge. Note that its conclusion mentions no Iris at
all — that is the point of an adequacy statement.

## What is trusted, and what is proved

Trusted (unchanged from today's Aeneas): that the ITree Aeneas emits corresponds
to the Rust source. This cannot be a Lean theorem, because neither LLBC's
semantics nor the translation is in Lean.

Proved (once the last `sorry` is discharged):

1. this file — `wpi` triple ⟹ no panic, no data race / out-of-bounds / type
   confusion, correct return value, and at `.total` termination;
2. `Lib/RwLockImpl.lean`, `Lib/ArcImpl.lean` — the standard-library primitives
   *implement* their interfaces, so they stop being axioms;
3. client refinements (e.g. against a pure model such as `MiniThemis.State`).
-/

namespace AeneasIris.Semantics

open Iris BI Aeneas.Data.Coinductive
open AeneasIris.Heap (HeapGS heapInterp)
open Aeneas.Std (Result RustEffect RustHeap Loc Cell Val HMap)

unseal Aeneas.Std.Result

/-! ## The logic side -/

/-- The hypothesis of the final theorem: in **every** Iris model, and for every
choice of later-credit setting, the triple is provable from nothing.

Quantifying over `GF` rather than fixing it is what lets the adequacy proof pick
a concrete model and allocate the heap ghost state itself; the client never sees
that.

Quantifying over `hlc` matters for a specific reason. The adequacy proof
instantiates it at **`HasLC.hasNoLC`**, because `fupd_plain_mask`
(`|={E,E'}=> P ⊢ |={E}=> P` for `Plain P`) is what lets the pure postcondition
`⌜φ v⌝` be read off at the empty mask, and iris-lean only provides the
`BIFUpdatePlainly` instance at `.hasNoLC` — later credits and fupd-plainly are
incompatible. Later credits are not needed here anyway: the `▷` that `stepH`
issues at `.part` is discharged by the `▷` slot of `|={∅}▷=>^[n]`, not by `£`.

The precondition is `emp` because `init` starts from the empty heap. For a
general initial heap `σ₀` it would instead be the points-to assertions for `σ₀`,
and nothing else in this file would change. -/
def ProvableSpec (m : Mode) {α : Type} (t : Result α) (φ : α → Prop) : Prop :=
  ∀ (GF : BundledGFunctors) (hlc : Iris.HasLC) [Iris.InvGS_gen hlc GF]
    [HeapGS.{0} GF],
    ⦃ emp ⦄ t @ (Rust.rustH (GF := GF) m) ; m ; ⊤ ⦃ v, ⌜φ v⌝ ⦄

/-! ## Total implies partial, on the hypothesis side

Proved, not `sorry`'d: it is evidence that `ProvableSpec` is stated at the right
granularity. It is exactly `Rust.iSpec_total_to_partial` lifted through the
`∀ GF, hlc`. It has to come *before* `adequacy_total`, which uses it to get the
first two conjuncts for free. -/

theorem ProvableSpec.total_to_part {α : Type} {t : Result α} {φ : α → Prop}
    (h : ProvableSpec .total t φ) : ProvableSpec .part t φ := by
  unfold ProvableSpec at h ⊢
  intro GF hlc hinv hheap
  exact Rust.iSpec_total_to_partial (h GF hlc)

/-! ## The final theorem -/

/-- **Final theorem — partial correctness.**

Proving one `wpi` triple at `.part` gives, for every schedule:

* the program never panics and never performs an undefined heap operation
  (`Safe`), and
* if the main thread returns, its value satisfies `φ`.

Nothing is claimed about termination: at `.part` the `step` events issue a `▷`,
Löb induction is available, and `divOK .part = True`, so a spinning or silently
diverging program is provable — and correspondingly permitted here. -/
theorem adequacy_part {α : Type} (t : Result α) (φ : α → Prop)
    (h : ProvableSpec .part t φ) :
    Safe t ∧ ∀ v, MayReturn t v → φ v :=
  ⟨safe_of_provable h, post_of_provable h⟩

/-! ## The `.total` plumbing

`Semantics/Soundness.lean` fixes `sysInv_of_provable` at `.part`, because that is
all `Safe` and `MayReturn` need. The two termination facts need the same
statement at `.total`; its proof is the same three lines, since `sysInv_init` and
`sysInv_reachesN` are both mode-generic. The rest is `safe_of_provable`'s shape
verbatim: fix the step count outside the logic, enter with `pure_soundness` +
`step_fupdN_soundness` at `.hasNoLC`, allocate the heap, and read the conclusion
off with the relevant `Termination.lean` lemma. -/

private theorem sysInv_of_provable_total {α : Type} {t : Result α} {φ : α → Prop}
    (h : ProvableSpec .total t φ) {n : Nat} {c : Config α}
    (hn : ReachesN n (init t) c)
    [Iris.InvGS_gen .hasNoLC SoundGF] [HeapGS.{0} SoundGF] :
    iprop(heapInterp (∅ : RustHeap.{0}))
      ⊢ iprop(|={⊤,∅}=> |={∅}▷=>^[n]
          SysInv (GF := SoundGF) .total (fun v => iprop(⌜φ v⌝)) c) := by
  have hwp := h SoundGF .hasNoLC
  refine .trans (sep_emp (PROP := IProp SoundGF)).2 ?_
  refine .trans (sep_mono_right hwp) ?_
  refine .trans (sysInv_init .total (fun v => iprop(⌜φ v⌝)) t) ?_
  exact BIFUpdate.mono (sysInv_reachesN .total _ hn)

/-- **No reachable configuration silently diverges.** `sysInv_not_diverging`,
run through the soundness plumbing. -/
private theorem not_diverging_of_provable {α : Type} {t : Result α} {φ : α → Prop}
    (h : ProvableSpec .total t φ) {c : Config α} (hr : Reaches (init t) c) :
    ¬ c.Diverging := by
  obtain ⟨n, hn⟩ := hr.toReachesN
  refine pure_soundness (PROP := IProp SoundGF) ?_
  refine step_fupdN_soundness (GF := SoundGF) (hlc := .hasNoLC) (n := n + 1) (m := 0) ?_
  intro Hinv
  have final : ∀ γ : GName,
      (Iris.ghost_map_auth (GF := SoundGF) (H := HMap) γ (DFrac.own 1)
          (∅ : HMap (Cell Val.{0})))
        ⊢ iprop(|={⊤,∅}=> |={∅}▷=>^[n + 1] ⌜¬ c.Diverging⌝) := by
    intro γ
    letI HG : HeapGS.{0} SoundGF := soundHeapGS γ
    show iprop(heapInterp (∅ : RustHeap.{0})) ⊢ _
    refine .trans (sysInv_of_provable_total h hn) (BIFUpdate.mono ?_)
    refine .trans (step_fupdN_mono (sysInv_not_diverging _ c)) ?_
    refine .trans (step_fupdN_le (Nat.le_succ n) (subset_refl ..)) ?_
    exact step_fupdN_S_fupd.mpr
  iintro _
  imod (Iris.ghost_map_alloc (GF := SoundGF) (K := Loc) (V := Cell Val.{0}) (H := HMap)
        (∅ : HMap (Cell Val.{0}))) with ⟨%γ, Hauth, -⟩
  iapply (BI.entails_wand (final γ))
  iexact Hauth

/-- **No reachable configuration admits an infinite execution.** `sysInv_sn`,
run through the same plumbing. -/
private theorem sn_of_provable {α : Type} {t : Result α} {φ : α → Prop}
    (h : ProvableSpec .total t φ) {c : Config α} (hr : Reaches (init t) c) :
    SN c := by
  obtain ⟨n, hn⟩ := hr.toReachesN
  refine pure_soundness (PROP := IProp SoundGF) ?_
  refine step_fupdN_soundness (GF := SoundGF) (hlc := .hasNoLC) (n := n + 1) (m := 0) ?_
  intro Hinv
  have final : ∀ γ : GName,
      (Iris.ghost_map_auth (GF := SoundGF) (H := HMap) γ (DFrac.own 1)
          (∅ : HMap (Cell Val.{0})))
        ⊢ iprop(|={⊤,∅}=> |={∅}▷=>^[n + 1] ⌜SN c⌝) := by
    intro γ
    letI HG : HeapGS.{0} SoundGF := soundHeapGS γ
    show iprop(heapInterp (∅ : RustHeap.{0})) ⊢ _
    refine .trans (sysInv_of_provable_total h hn) (BIFUpdate.mono ?_)
    refine .trans (step_fupdN_mono (sysInv_sn _ c)) ?_
    refine .trans (step_fupdN_le (Nat.le_succ n) (subset_refl ..)) ?_
    exact step_fupdN_S_fupd.mpr
  iintro _
  imod (Iris.ghost_map_alloc (GF := SoundGF) (K := Loc) (V := Cell Val.{0}) (H := HMap)
        (∅ : HMap (Cell Val.{0}))) with ⟨%γ, Hauth, -⟩
  iapply (BI.entails_wand (final γ))
  iexact Hauth

/-- **Total correctness, termination half.** -/
theorem terminates_of_provable {α : Type} {t : Result α} {φ : α → Prop}
    (h : ProvableSpec .total t φ) : Terminates t :=
  fun _ hr => ⟨sn_of_provable h hr, not_diverging_of_provable h hr⟩

/-- **Final theorem — total correctness.**

At `.total` the `step` events issue no modality and `divOK .total = False`, so
the least fixpoint has to be well-founded: every execution terminates and no
thread silently diverges.

⚠️ The `Mode` argument occurs twice — once in `Rust.rustH m` (which fixes
whether `stepH` issues a `▷`) and once as the `wpi` parameter (which fixes
`divOK`) — and Lean does not force the two to agree: `Rust.rustH .part` read at
`.total` is well-typed, and it is unsound to conclude termination from it, since
`▷` at every step makes Löb available while `divOK = False` claims divergence is
excluded. Writing both as the same `m`, as `ProvableSpec` does, is what rules
that combination out. This mirrors the artifact, where `step_adequacy` takes `m`
explicitly and demands `⌜m = Later⌝ → £ n`. -/
theorem adequacy_total {α : Type} (t : Result α) (φ : α → Prop)
    (h : ProvableSpec .total t φ) :
    Safe t ∧ (∀ v, MayReturn t v → φ v) ∧ Terminates t := by
  have hpart := h.total_to_part
  exact ⟨safe_of_provable hpart, post_of_provable hpart, terminates_of_provable h⟩

/-! ## What `Safe` actually says

These two are proved, not `sorry`'d: they are the check that the definitions in
`Machine.lean` really do deliver the properties claimed for them. -/

/-- No reachable configuration is about to panic. -/
theorem no_panic {α : Type} {t : Result α} (hs : Safe t)
    {c : Config α} (hr : Reaches (init t) c) {t' : Result α} (hf : c.focus = some t') :
    ¬ Panics t' :=
  fun hp => hs c hr ⟨t', hf, .inl hp⟩

/-- No reachable configuration is about to perform an undefined heap operation.
Since `AccessState` makes a racing `writeAcquire` undefined, this subsumes
data-race freedom; since a type-mismatched `load_at` is undefined, it subsumes
type safety of the dynamically typed heap. -/
theorem no_undefined_heap_op {α : Type} {t : Result α} (hs : Safe t)
    {c : Config α} (hr : Reaches (init t) c) {t' : Result α} (hf : c.focus = some t') :
    ¬ StuckOn c.heap t' :=
  fun hp => hs c hr ⟨t', hf, .inr hp⟩

/-! ## Total implies partial, on the hypothesis side

See `ProvableSpec.total_to_part`, above — it has to precede `adequacy_total`,
which is its first consumer. -/

end AeneasIris.Semantics
