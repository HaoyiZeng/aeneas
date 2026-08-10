import AeneasIris.Rules
import AeneasIris.Translate
import Aeneas.Std.WP
import Aeneas.Std.Spec
import Aeneas.Tactic.Step.Step

/-!
# `iSpec`: `wpi` as a spec judgment Aeneas' `step` tactic understands

`Aeneas.Std.Spec` exposes an extension point — `SpecInfo` plus
`#register_spec_info` — that makes the `step` tactic generic over the spec
judgment. `dspec` already uses it to inherit *every* `spec` lemma through a
`LiftingInfo`. This file does the same for `wpi`.

## Why a precondition

Aeneas' `spec` is a binary judgment, `spec t p` — no precondition, because a
pure computation owns nothing. A separation-logic weakest precondition needs
one, so `iSpec` carries it:

```
iSpec H P t Φ M  :=  P ⊢ wpi_mask GF H t Φ M
```

This is not a wrapper in any real sense: an Iris proof-mode goal *is* an
`Entails`, with the hypothesis context reified as the left-hand side. Printing
one with `pp.notation false` gives `Entails (sep P Q) (wpi_mask …)`. So moving
between proof mode and `iSpec` is a change of head symbol, nothing more.

`iSpec` is a `def` rather than an `abbrev` on purpose: `step` reads the head
symbol of the goal with `withApp` and looks it up in the `SpecInfo` table, so
the head has to be `iSpec` and not `Entails`.

## Why the lifting carries the frame

`iqimp_spec` hands the continuation exactly `Φ v`. If the lifting of a pure
`spec` had postcondition `⌜p v⌝`, every resource held across the call would be
*discarded*. `spec_to_iSpec` therefore concludes with `P ∗ ⌜p v⌝` — sound
because `spec t p` forces `t = ok x`, and a pure fact is entailed by anything.
-/

namespace AeneasIris

open Iris BI Aeneas.Data.Coinductive

/-! ## The judgment

Binders are written out rather than taken from `variable`s: `step` applies
`mk_spec_mono` / `mk_spec_bind` positionally, so their order is part of the
interface. -/

def iqimp {hlc : Iris.HasLC} {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]
    {α : Type} (Φ Ψ : Post GF α) : Prop :=
  ∀ v, Φ v ⊢ Ψ v

theorem iqimp_iff {hlc : Iris.HasLC} {GF : BundledGFunctors}
    [Iris.InvGS_gen hlc GF] {α : Type} (Φ Ψ : Post GF α) :
    iqimp Φ Ψ ↔ ∀ v, Φ v ⊢ Ψ v := Iff.rfl

theorem pure_entails_iff {GF : BundledGFunctors} (φ : Prop) (W : IProp GF) :
    (iprop(⌜φ⌝) ⊢ W) ↔ (φ → (⊢ W)) := by
  constructor
  · intro h hφ; exact .trans (BI.pure_intro hφ) h
  · intro h; exact BI.pure_elim' h

open Aeneas.Std (Result RustEffect)

unseal Aeneas.Std.Result

def iSpecT {hlc : Iris.HasLC} {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]
    {E : Effect} [RustEffect -< E]
    {α : Type} (H : Handler E GF)
    (t : Result α) (Φ : Post GF α) (M : CoPset) : Prop :=
  ⊢ wpi_mask GF H (ITree.translate t) Φ M

def iqimpT_spec {hlc : Iris.HasLC} {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]
    {E : Effect} [RustEffect -< E]
    {α β : Type} (H : Handler E GF)
    (Φ : Post GF α) (k : α → Result β) (Ψ : Post GF β) (M : CoPset) : Prop :=
  ∀ v, Φ v ⊢ wpi_mask GF H (ITree.translate (k v)) Ψ M

theorem iSpecT_mono' {hlc : Iris.HasLC} {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]
    {E : Effect} [RustEffect -< E]
    {α : Type} {H : Handler E GF} {M : CoPset} {Ψ : Post GF α}
    {t : Result α} {Φ : Post GF α}
    (h : iSpecT H t Φ M) (hq : iqimp Φ Ψ) : iSpecT H t Ψ M := by
  refine .trans h ?_
  iintro Hwp
  iapply (wpi_wand (H := H) (ITree.translate t) Φ Ψ M) $$ [] Hwp
  iintro %v HΦ
  iapply BI.entails_wand (hq v)
  iexact HΦ

theorem iSpecT_bind' {hlc : Iris.HasLC} {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]
    {E : Effect} [RustEffect -< E]
    {α β : Type} {H : Handler E GF} {M : CoPset}
    {k : α → Result β} {Ψ : Post GF β} {t : Result α} {Φ : Post GF α}
    (h : iSpecT H t Φ M) (hk : iqimpT_spec H Φ k Ψ M) :
    iSpecT H (t >>= k) Ψ M := by
  refine .trans h ?_
  show _ ⊢ wpi_mask GF H (ITree.translate (t >>= k)) Ψ M
  rw [translate_bind]
  refine .trans ?_ (wpi_bind (H := H) (ITree.translate t) (fun a => ITree.translate (k a)) Ψ M)
  iintro Hwp
  iapply (wpi_wand (H := H) (ITree.translate t) Φ
    (fun v => wpi_mask GF H (ITree.translate (k v)) Ψ M) M) $$ [] Hwp
  iintro %v HΦ
  iapply BI.entails_wand (hk v)
  iexact HΦ

theorem iqimpT_spec_def {hlc : Iris.HasLC} {GF : BundledGFunctors}
    [Iris.InvGS_gen hlc GF] {E : Effect} [RustEffect -< E] {α β : Type} (H : Handler E GF)
    (Φ : Post GF α) (k : α → Result β) (Ψ : Post GF β) (M : CoPset) :
    iqimpT_spec H Φ k Ψ M = ∀ v, Φ v ⊢ wpi_mask GF H (ITree.translate (k v)) Ψ M := rfl

theorem emp_valid_iSpecT {hlc : Iris.HasLC} {GF : BundledGFunctors}
    [Iris.InvGS_gen hlc GF] {E : Effect} [RustEffect -< E] {α : Type} (H : Handler E GF)
    (t : Result α) (Φ : Post GF α) (M : CoPset) :
    (⊢ wpi_mask GF H (ITree.translate t) Φ M) ↔ iSpecT H t Φ M := Iff.rfl

/-- Every `⦃⦄` lemma of the Aeneas standard library, as an `iSpecT`. -/
theorem spec_to_iSpecT {hlc : Iris.HasLC} {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]
    {E : Effect} [RustEffect -< E]
    {H : Handler E GF} {α : Type} {t : Result α} {p : Aeneas.Std.WP.Post α}
    {M : CoPset} (h : Aeneas.Std.WP.spec t p) :
    iSpecT H t (fun v => iprop(⌜p v⌝)) M := by
  cases h
  rename_i x hp
  show ⊢ wpi_mask GF H (ITree.translate (ITree.ret x)) _ M
  rw [itree_ret_translate]
  exact .trans (BI.pure_intro hp) (wpi_ret (H := H) x (fun v => iprop(⌜p v⌝)) M)

@[simp] theorem iSpecT_ok {hlc : Iris.HasLC} {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]
    {E : Effect} [RustEffect -< E] {H : Handler E GF} {α : Type}
    (v : α) (Φ : Post GF α) (M : CoPset) :
    iSpecT H (Result.ok v) Φ M  ↔  (⊢ |={M}=> Φ v) := by
  /- `Result.ok v` is `ITree.ret v`, but `Result` is irreducible outside its own
  file, so the `ret` equation has to be pointed at the goal explicitly. -/
  unfold iSpecT
  have hr : ITree.translate (E₂ := E) (Result.ok v) = ITree.ret v := itree_ret_translate v
  rw [hr]
  constructor
  · intro h
    exact .trans h (wpi_ret' (H := H) v Φ M).mpr
  · intro h
    exact .trans h (wpi_ret' (H := H) v Φ M).mp

/-! ## The judgment with a precondition

`iSpecT` has no precondition, so it can only state goals that hold from `emp`.
That is useless for a heap: `{l ↦ v} t {Q}` is the shape every interesting
triple has.

`SpecInfo` has no `pre_index`, which I read at first as "preconditions are
impossible". That is wrong. `step` supplies only the program and the post and
lets unification do the rest, and `P` *occurs in the conclusion* of both
`mk_spec_mono` and `mk_spec_bind` — so unifying that conclusion with the goal
determines it. A precondition costs nothing but an extra index. -/

def iSpecP {hlc : Iris.HasLC} {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]
    {E : Effect} [RustEffect -< E]
    {α : Type} (H : Handler E GF) (P : IProp GF)
    (t : Result α) (Φ : Post GF α) (M : CoPset) : Prop :=
  P ⊢ wpi_mask GF H (ITree.translate t) Φ M

def iqimpP_spec {hlc : Iris.HasLC} {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]
    {E : Effect} [RustEffect -< E]
    {α β : Type} (H : Handler E GF)
    (Φ : Post GF α) (k : α → Result β) (Ψ : Post GF β) (M : CoPset) : Prop :=
  ∀ v, Φ v ⊢ wpi_mask GF H (ITree.translate (k v)) Ψ M

theorem iSpecP_mono' {hlc : Iris.HasLC} {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]
    {E : Effect} [RustEffect -< E]
    {α : Type} {H : Handler E GF} {P : IProp GF} {M : CoPset} {Ψ : Post GF α}
    {t : Result α} {Φ : Post GF α}
    (h : iSpecP H P t Φ M) (hq : iqimp Φ Ψ) : iSpecP H P t Ψ M := by
  refine .trans h ?_
  iintro Hwp
  iapply (wpi_wand (H := H) (ITree.translate t) Φ Ψ M) $$ [] Hwp
  iintro %v HΦ
  iapply BI.entails_wand (hq v)
  iexact HΦ

theorem iSpecP_bind' {hlc : Iris.HasLC} {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]
    {E : Effect} [RustEffect -< E]
    {α β : Type} {H : Handler E GF} {P : IProp GF} {M : CoPset}
    {k : α → Result β} {Ψ : Post GF β} {t : Result α} {Φ : Post GF α}
    (h : iSpecP H P t Φ M) (hk : iqimpP_spec H Φ k Ψ M) :
    iSpecP H P (t >>= k) Ψ M := by
  refine .trans h ?_
  show _ ⊢ wpi_mask GF H (ITree.translate (t >>= k)) Ψ M
  rw [translate_bind]
  refine .trans ?_ (wpi_bind (H := H) (ITree.translate t) (fun a => ITree.translate (k a)) Ψ M)
  iintro Hwp
  iapply (wpi_wand (H := H) (ITree.translate t) Φ
    (fun v => wpi_mask GF H (ITree.translate (k v)) Ψ M) M) $$ [] Hwp
  iintro %v HΦ
  iapply BI.entails_wand (hk v)
  iexact HΦ

/-- The elimination that recovers the precondition.

`step` leaves the continuation as `⌜p v⌝ ∗ P ⊢ W`; this turns it back into
`p v → (P ⊢ W)`, i.e. a pure hypothesis plus a goal that is again an `iSpecP`
with the *same* `P`. The framing is therefore transient: `P` is threaded, not
accumulated. -/
/- `∧`, not `∗`: dropping a `⌜φ⌝` from `⌜φ⌝ ∗ P` needs the pure proposition to
be affine, whereas `⌜φ⌝ ∧ P ⊢ P` is unconditional. Nothing is gained by the
separating version — `P` is duplicated into neither. -/
theorem and_pure_entails_iff {GF : BundledGFunctors} (φ : Prop) (P W : IProp GF) :
    (iprop(⌜φ⌝ ∧ P) ⊢ W) ↔ (φ → (P ⊢ W)) := by
  constructor
  · intro h hφ
    exact .trans (BI.and_intro (BI.pure_intro hφ) .rfl) h
  · intro h
    exact BI.pure_elim_left h

theorem iqimpP_spec_def {hlc : Iris.HasLC} {GF : BundledGFunctors}
    [Iris.InvGS_gen hlc GF] {E : Effect} [RustEffect -< E] {α β : Type} (H : Handler E GF)
    (Φ : Post GF α) (k : α → Result β) (Ψ : Post GF β) (M : CoPset) :
    iqimpP_spec H Φ k Ψ M = ∀ v, Φ v ⊢ wpi_mask GF H (ITree.translate (k v)) Ψ M := rfl

theorem entails_iSpecP {hlc : Iris.HasLC} {GF : BundledGFunctors}
    [Iris.InvGS_gen hlc GF] {E : Effect} [RustEffect -< E] {α : Type} (H : Handler E GF)
    (P : IProp GF) (t : Result α) (Φ : Post GF α) (M : CoPset) :
    (P ⊢ wpi_mask GF H (ITree.translate t) Φ M) ↔ iSpecP H P t Φ M := Iff.rfl

/-- The lifting, with framing.

An Aeneas `⦃⦄` lemma says the computation is pure and returns a value
satisfying `p`. Lifting it must *carry `P` across*, otherwise the precondition
is consumed by the first pure call and nothing is left for the heap operations
that follow. -/
theorem spec_to_iSpecP {hlc : Iris.HasLC} {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]
    {E : Effect} [RustEffect -< E]
    {H : Handler E GF} {P : IProp GF} {α : Type} {t : Result α}
    {p : Aeneas.Std.WP.Post α} {M : CoPset} (h : Aeneas.Std.WP.spec t p) :
    iSpecP H P t (fun v => iprop(⌜p v⌝ ∧ P)) M := by
  cases h
  rename_i x hp
  show _ ⊢ wpi_mask GF H (ITree.translate (ITree.ret x)) _ M
  rw [itree_ret_translate]
  refine .trans ?_ (wpi_ret (H := H) x (fun v => iprop(⌜p v⌝ ∧ P)) M)
  exact BI.and_intro (BI.pure_intro hp) .rfl

/-! ## Sequencing an Aeneas block inside a larger program

`iSpecT_bind'` — the lemma `step` is registered with — is *homogeneous*: both
the head and the continuation must be `Result`. A mixed program breaks that,
because its continuation performs events Aeneas has no name for, so its type is
`ITree E`, not `Result`.

The heterogeneous bind below is what bridges the two. It is `wpi_bind`
specialised so that the *head* is recognisably an `iSpecT`; `step` can then fire
on that residual goal, because its program argument is once again a literal
`Result` term. There is no way to register this with `#register_spec_info`: a
`SpecInfo` describes one judgment, and this lemma relates two. -/

/-- Peel a leading Aeneas block off a mixed program.

The residual goal is definitionally an `iSpecT`, which `step_aeneas` exploits. -/
theorem wpi_bind_translate {hlc : Iris.HasLC} {GF : BundledGFunctors}
    [Iris.InvGS_gen hlc GF] {E : Effect} [RustEffect -< E] {H : Handler E GF}
    {α β : Type} (t : Result α) (k : α → ITree E β) (Φ : Post GF α) (Ψ : Post GF β)
    (M : CoPset) (h : iSpecT H t Φ M) (hk : ∀ v, Φ v ⊢ wpi_mask GF H (k v) Ψ M) :
    ⊢ wpi_mask GF H (ITree.translate t >>= k) Ψ M := by
  refine .trans h ?_
  refine .trans ?_ (wpi_bind (H := H) (ITree.translate t) k Ψ M)
  iintro Hwp
  iapply (wpi_wand (H := H) (ITree.translate t) Φ
    (fun v => wpi_mask GF H (k v) Ψ M) M) $$ [] Hwp
  iintro %v HΦ
  iapply BI.entails_wand (hk v)
  iexact HΦ

/-- Consume a leading Aeneas block with `step`.

Expands to the three moves that pattern always needs: split the bind, change
the head symbol to `iSpecT` (a `show` — the two are definitionally equal), then
`step`. -/
macro "step_aeneas" : tactic =>
  `(tactic| (refine .trans ?_ (wpi_bind _ _ _ _); show iSpecT _ _ _ _; step))

/- The same registration for the effect-polymorphic judgment. Both may be
registered at once: `step` dispatches on the head constant of the goal. -/
#register_spec_info {
    spec_name := ``AeneasIris.iSpecT
    arity := 10
    program_index := 7
    post_index := 8
    mk_spec_mono := ``AeneasIris.iSpecT_mono'
    mk_spec_mono_skip_args := 9
    mk_spec_bind := ``AeneasIris.iSpecT_bind'
    mk_spec_bind_skip_args := 11
    uncurry_elim_tactics := #[]
    qimp_elim_tactics := #[``AeneasIris.iqimpT_spec_def, ``AeneasIris.pure_entails_iff,
                           ``AeneasIris.emp_valid_iSpecT, ``AeneasIris.iqimp_iff]
    to_mvcgen := .none
    liftings := #[
      { from_statement := ``Aeneas.Std.WP.spec
        conversion_thm := ``AeneasIris.spec_to_iSpecT
        conversion_thm_inferred_args := 10 }
    ]
  }

/- `@iSpecP hlc GF inst E sub α H P t Φ M` — arity 11, program 8, post 9. -/
#register_spec_info {
    spec_name := ``AeneasIris.iSpecP
    arity := 11
    program_index := 8
    post_index := 9
    mk_spec_mono := ``AeneasIris.iSpecP_mono'
    mk_spec_mono_skip_args := 10
    mk_spec_bind := ``AeneasIris.iSpecP_bind'
    mk_spec_bind_skip_args := 12
    uncurry_elim_tactics := #[]
    qimp_elim_tactics := #[``AeneasIris.iqimpP_spec_def, ``AeneasIris.and_pure_entails_iff,
                           ``AeneasIris.entails_iSpecP, ``AeneasIris.iqimp_iff]
    to_mvcgen := .none
    liftings := #[
      { from_statement := ``Aeneas.Std.WP.spec
        conversion_thm := ``AeneasIris.spec_to_iSpecP
        conversion_thm_inferred_args := 11 }
    ]
  }

/-- Consume a leading Aeneas block from inside the Iris proof mode.

`istop` turns the proof-mode goal into the plain entailment `P ⊢ wp t Q`, which
*is* an `iSpecP` — so `step` applies, replaying the function's `⦃⦄` lemma and
framing `P` across it. `istart` hands the residual goal back to the proof mode. -/
macro "istep" : tactic =>
  `(tactic| ((first | istop | skip); show iSpecP _ _ _ _ _; step; (first | istart | skip)))

end AeneasIris
