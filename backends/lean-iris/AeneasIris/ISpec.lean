import AeneasIris.Rules
import Aeneas.Std.WP
import Aeneas.Std.Spec
import Aeneas.Tactic.Step.Step

/-!
# `iSpec`: `wpi` as a spec judgment Aeneas' `step` tactic understands

`Aeneas.Std.Spec` exposes an extension point — `SpecInfo` plus
`#register_spec_info` — that makes the `step` tactic generic over the spec
judgment. `dspec` already uses it to inherit *every* `spec` lemma through a
`LiftingInfo`. This file does the same for `wpi`, so that the standard
library's `⦃⦄` lemmas replay inside a separation-logic proof without being
restated.

## The judgment

```
iSpec H P t Φ M  :=  P ⊢ wpi_mask GF H t Φ M
```

An Iris proof-mode goal *is* an `Entails`, with the hypothesis context reified
as the left-hand side; printing one with `pp.notation false` gives
`Entails (sep P Q) (wpi_mask …)`. So `iSpec` is not a wrapper in any real
sense, and moving between proof mode and the judgment is a change of head
symbol — which is what `istep` does with `istop` / `show` / `istart`.

`iSpec` is a `def` rather than an `abbrev` on purpose: `step` reads the head
symbol of the goal with `withApp` and looks it up in the `SpecInfo` table, so
the head has to be `iSpec` and not `Entails`.

There is one judgment, not two. `P := emp` covers the no-precondition case,
because `⊢ Q` is *definitionally* `emp ⊢ Q` (`BIBase.EmpValid`) — and `istop`
emits `EmpValid` exactly when the proof-mode context is empty.

## Why the lifting carries the frame

`iqimp_spec` hands the continuation exactly `Φ v`. If the lifting of a pure
`spec` had postcondition `⌜p v⌝`, every resource held across the call would be
*discarded*. `spec_to_iSpec` therefore concludes with `⌜p v⌝ ∧ P`.

This is sound precisely because `spec t p` forces `t = ok x`: a pure
computation owns nothing, so threading the whole precondition across it is
safe. For an operation that *consumes* a resource it would not be — which is
why the heap rules are applied by hand rather than registered here. `step`
communicates only the program and the post, so a rule whose postcondition
depends on which part of the context it consumed cannot be driven by it.

`∧` rather than `∗`: discharging a `⌜φ⌝` from `⌜φ⌝ ∗ P` needs the pure
proposition to be affine, whereas `⌜φ⌝ ∧ P ⊢ P` is unconditional. The
separating version buys nothing — `P` is duplicated into neither.
-/

namespace AeneasIris

open Iris BI Aeneas.Data.Coinductive
open Aeneas.Std (Result RustEffect)

unseal Aeneas.Std.Result

/-! ## The judgment

Binders are written out rather than taken from `variable`s: `step` applies
`mk_spec_mono` / `mk_spec_bind` positionally, so their order is part of the
interface. -/

def iSpec {hlc : Iris.HasLC} {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]
    {α : Type} (H : Handler RustEffect GF) (P : IProp GF)
    (t : Result α) (Φ : Post GF α) (M : CoPset) : Prop :=
  P ⊢ wpi_mask GF H t Φ M

/-- The Iris counterpart of `qimp`. -/
def iqimp {hlc : Iris.HasLC} {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]
    {α : Type} (Φ Ψ : Post GF α) : Prop :=
  ∀ v, Φ v ⊢ Ψ v

/-- The Iris counterpart of `qimp_spec`. The continuation is verified under the
previous postcondition — an entailment rather than an `iSpec`, because there is
no precondition left to speak of at that point. -/
def iqimp_spec {hlc : Iris.HasLC} {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]
    {α β : Type} (H : Handler RustEffect GF)
    (Φ : Post GF α) (k : α → Result β) (Ψ : Post GF β) (M : CoPset) : Prop :=
  ∀ v, Φ v ⊢ wpi_mask GF H (k v) Ψ M

/-! ## The two lemmas `step` needs -/

/-- `mk_spec_mono`. -/
theorem iSpec_mono' {hlc : Iris.HasLC} {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]
    {α : Type} {H : Handler RustEffect GF} {P : IProp GF} {M : CoPset} {Ψ : Post GF α}
    {t : Result α} {Φ : Post GF α}
    (h : iSpec H P t Φ M) (hq : iqimp Φ Ψ) : iSpec H P t Ψ M := by
  refine .trans h ?_
  iintro Hwp
  iapply (wpi_wand (H := H) t Φ Ψ M) $$ [] Hwp
  iintro %v HΦ
  iapply BI.entails_wand (hq v)
  iexact HΦ

/-- `mk_spec_bind`. -/
theorem iSpec_bind' {hlc : Iris.HasLC} {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]
    {α β : Type} {H : Handler RustEffect GF} {P : IProp GF} {M : CoPset}
    {k : α → Result β} {Ψ : Post GF β} {t : Result α} {Φ : Post GF α}
    (h : iSpec H P t Φ M) (hk : iqimp_spec H Φ k Ψ M) :
    iSpec H P (t >>= k) Ψ M := by
  refine .trans h ?_
  show _ ⊢ wpi_mask GF H (ITree.bind t k) Ψ M
  refine .trans ?_ (wpi_bind (H := H) t k Ψ M)
  iintro Hwp
  iapply (wpi_wand (H := H) t Φ (fun v => wpi_mask GF H (k v) Ψ M) M) $$ [] Hwp
  iintro %v HΦ
  iapply BI.entails_wand (hk v)
  iexact HΦ

/-! ## The eliminations

Registered as `qimp_elim_tactics`, not as global `@[simp]` lemmas.
`entails_iSpec` folds a definition into itself, which loops as a simp lemma;
`and_pure_entails_iff` matches any `⌜φ⌝ ∧ P ⊢ W` and is far too broad to be let
loose. Inside the residual goal `step` produces, both are exactly right. -/

theorem iqimp_iff {hlc : Iris.HasLC} {GF : BundledGFunctors}
    [Iris.InvGS_gen hlc GF] {α : Type} (Φ Ψ : Post GF α) :
    iqimp Φ Ψ ↔ ∀ v, Φ v ⊢ Ψ v := Iff.rfl

theorem iqimp_spec_def {hlc : Iris.HasLC} {GF : BundledGFunctors}
    [Iris.InvGS_gen hlc GF] {α β : Type} (H : Handler RustEffect GF)
    (Φ : Post GF α) (k : α → Result β) (Ψ : Post GF β) (M : CoPset) :
    iqimp_spec H Φ k Ψ M = ∀ v, Φ v ⊢ wpi_mask GF H (k v) Ψ M := rfl

theorem entails_iSpec {hlc : Iris.HasLC} {GF : BundledGFunctors}
    [Iris.InvGS_gen hlc GF] {α : Type} (H : Handler RustEffect GF)
    (P : IProp GF) (t : Result α) (Φ : Post GF α) (M : CoPset) :
    (P ⊢ wpi_mask GF H t Φ M) ↔ iSpec H P t Φ M := Iff.rfl

/-- Recovers the precondition after a lifted pure call: the pure fact becomes a
Lean hypothesis and the goal is again an `iSpec` with the *same* `P`. The
framing is therefore transient — `P` is threaded, not accumulated. -/
theorem and_pure_entails_iff {GF : BundledGFunctors} (φ : Prop) (P W : IProp GF) :
    (iprop(⌜φ⌝ ∧ P) ⊢ W) ↔ (φ → (P ⊢ W)) := by
  constructor
  · intro h hφ
    exact .trans (BI.and_intro (BI.pure_intro hφ) .rfl) h
  · intro h
    exact BI.pure_elim_left h

theorem pure_entails_iff {GF : BundledGFunctors} (φ : Prop) (W : IProp GF) :
    (iprop(⌜φ⌝) ⊢ W) ↔ (φ → (⊢ W)) := by
  constructor
  · intro h hφ; exact .trans (BI.pure_intro hφ) h
  · intro h; exact BI.pure_elim' h

/-- Re-establish the head symbol `step` dispatches on.

`show iSpec _ _ _ _ _` expresses the same thing, but elaborating that type from
five holes asks for `InvGS_gen ?hlc ?GF` before anything has determined `GF`,
and instance resolution gets stuck. Applying a lemma unifies its *conclusion*
with the goal first, so every argument is fixed before an instance is sought. -/
theorem iSpec_intro {hlc : Iris.HasLC} {GF : BundledGFunctors}
    [Iris.InvGS_gen hlc GF] {α : Type} {H : Handler RustEffect GF} {P : IProp GF}
    {t : Result α} {Φ : Post GF α} {M : CoPset}
    (h : iSpec H P t Φ M) : P ⊢ wpi_mask GF H t Φ M := h

/-! ## The lifting -/

/-- Every `⦃⦄` lemma of the Aeneas standard library, as an `iSpec`. -/
theorem spec_to_iSpec {hlc : Iris.HasLC} {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]
    {H : Handler RustEffect GF} {P : IProp GF} {α : Type} {t : Result α}
    {p : Aeneas.Std.WP.Post α} {M : CoPset} (h : Aeneas.Std.WP.spec t p) :
    iSpec H P t (fun v => iprop(⌜p v⌝ ∧ P)) M := by
  cases h
  rename_i x hp
  show _ ⊢ wpi_mask GF H (ITree.ret x) _ M
  refine .trans ?_ (wpi_ret (H := H) x (fun v => iprop(⌜p v⌝ ∧ P)) M)
  exact BI.and_intro (BI.pure_intro hp) .rfl

@[simp] theorem iSpec_ok {hlc : Iris.HasLC} {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]
    {H : Handler RustEffect GF} {P : IProp GF} {α : Type}
    (v : α) (Φ : Post GF α) (M : CoPset) :
    iSpec H P (Result.ok v) Φ M  ↔  (P ⊢ |={M}=> Φ v) := by
  /- `Result.ok v` *is* `ITree.ret v`, so this is `wpi_ret'` — which is already
  an `⊣⊢` — transported along the entailment. `⊣⊢` cannot be `rw`n; compose
  with `.mp` / `.mpr` instead. -/
  unfold iSpec
  constructor
  · intro h; exact .trans h (wpi_ret' (H := H) v Φ M).mpr
  · intro h; exact .trans h (wpi_ret' (H := H) v Φ M).mp

/-! ## Registration

The indices are positional and were read off the explicit signature:

```
@iSpec hlc GF inst α H P t Φ M     -- arity 9, program at 6, post at 7
```

`skip_args` counts the binders `step` must solve by unification before it
supplies the program, the post and the step theorem — everything up to but not
including `t`. They line up only if `iSpec_mono'` and `iSpec_bind'` keep the
binder order written above. -/

open Aeneas in
#register_spec_info {
    spec_name := ``AeneasIris.iSpec
    arity := 9
    program_index := 6
    post_index := 7
    mk_spec_mono := ``AeneasIris.iSpec_mono'
    mk_spec_mono_skip_args := 8
    mk_spec_bind := ``AeneasIris.iSpec_bind'
    mk_spec_bind_skip_args := 10
    uncurry_elim_tactics := #[]
    /- `entails_iSpec` is deliberately absent. All of these go into a *single*
    `simp` call (`Step.lean`, "eliminating `qimp_spec` and `qimp`"), so the order
    of the list buys nothing, and on a residual `⌜φ⌝ ∧ P ⊢ wpi_mask …` both it
    and `and_pure_entails_iff` match. Folding into `iSpec` wins, and the pure
    fact is then stranded in the precondition instead of becoming a hypothesis.
    Leaving it out costs nothing: `istep` re-establishes the head symbol with a
    `show` on its way in. -/
    qimp_elim_tactics := #[``AeneasIris.iqimp_spec_def, ``AeneasIris.and_pure_entails_iff,
                           ``AeneasIris.iqimp_iff]
    to_mvcgen := .none
    liftings := #[
      { from_statement := ``Aeneas.Std.WP.spec
        conversion_thm := ``AeneasIris.spec_to_iSpec
        conversion_thm_inferred_args := 9 }
    ]
  }

end AeneasIris
