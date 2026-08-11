import AeneasIris.ISpec
import AeneasIris.RustHandler
import Iris.BI.WeakestPre

/-!
# Tactics

Two kinds of step, and they are automated differently.

**A pure Aeneas call** is replayed from the `@[step]` database by `istep`.
`istop` turns the proof-mode goal into the plain entailment `P ⊢ wp t Q`, which
*is* an `iSpec`, so `step` applies; the framing lifting threads `P` across the
call and `and_pure_entails_iff` normalises it back to exactly `P`. Nothing has
to be restated: all ~167 `⦃⦄` lemmas are reachable this way.

**An operation that touches the heap** cannot go through `step` at all. `step`
communicates only the program and the postcondition, and a rule that *consumes*
part of the context has a postcondition depending on which part — there is no
slot for that, and no frame inference. So `iheap` applies the rule by hand and
lets the Iris proof mode do the framing, which is what Coq Iris does for
`wp_load` and friends. The frame is never named: it simply stays in the context.

## The shape of `iheap`

```
iapply wpi_bind          -- peel the leading operation (skipped in tail position)
iapply rule              -- goal becomes  ⊢ lat m (pre ∗ (post -∗ |={M}=> …))
simp only [lat_*]        -- `lat` is a def; `inext` and `isplitl` cannot see through it
inext                    -- introduce the ▷ *and* strip one off every context hypothesis
isplitl [h]              -- h pays for `pre`; everything else goes to the continuation
```

The `inext` is the load-bearing step for recursion: the `▷` it strips off the
Löb hypothesis is what licenses using it at the recursive call. `lat_intro`
would discharge the modality too, but it *discards* the `▷`, so it is only
usable when no Löb induction is in play.

`simp only [lat_identity, lat_later]` requires the modality to be concrete.
That is not a restriction in practice: a proof is either about partial
correctness (`.later`) or total correctness (`.identity`), never both, so the
handler is instantiated before the proof begins.
-/

namespace AeneasIris

open Iris BI Aeneas.Data.Coinductive
open Aeneas.Std (Result RustEffect)

unseal Aeneas.Std.Result

/-- `wpi_bind` stated with `Result`'s own bind.

Spelled with `Aeneas.Std.bind` rather than `>>=`: this file `unseal`s `Result`,
so a `>>=` written here would resolve to `ITree`'s `Monad` instance, while a
`do` block in a client — where `Result` is opaque — resolves to `Result`'s. The
two are definitionally equal and syntactically different, and `iapply` unifies
at reducible transparency, so the mismatch is fatal. Naming the function the
instance is built from sidesteps the choice. -/
theorem wpi_bind_result {hlc : Iris.HasLC} {GF : BundledGFunctors}
    [Iris.InvGS_gen hlc GF] {α β : Type} {H : Handler RustEffect GF}
    (t : Result α) (k : α → Result β) (Φ : Post GF β) (M : CoPset) :
    wpi_mask GF H t (fun v => wpi_mask GF H (k v) Φ M) M
      ⊢ wpi_mask GF H (Aeneas.Std.bind t k) Φ M :=
  wpi_bind (H := H) t k Φ M

/-- `wpi_ret` stated with `Result.ok`, for the same reason as
`wpi_bind_result`: a client writes `Result.ok`, and `iapply` will not unfold it
to `ITree.ret`. -/
theorem wpi_ret_result {hlc : Iris.HasLC} {GF : BundledGFunctors}
    [Iris.InvGS_gen hlc GF] {α : Type} {H : Handler RustEffect GF}
    (v : α) (Φ : Post GF α) (M : CoPset) :
    Φ v ⊢ wpi_mask GF H (Result.ok v) Φ M :=
  wpi_ret (H := H) v Φ M


/-- The core of `istep`, without the context bookkeeping.

The whole of `step` is reused: the `@[step]` lookup, the lifting through
`spec_to_iSpec`, the bind detection and the `qimp` elimination are all its own.
All this adds is the head symbol it dispatches on. Its arguments are forwarded
verbatim, so `as ⟨…⟩`, `with thm` and the configuration options are inherited
rather than reimplemented. -/
macro "istep_core" args:Aeneas.Step.stepArgs : tactic =>
  `(tactic| ((first | istop | skip);
             (first | refine iSpec_intro ?_ | show iSpec _ _ _ _ _);
             step $args))

open Lean Elab Tactic Meta in
/-- Consume a leading *pure* Aeneas call, keeping the proof-mode context.

`istep_core` alone loses the hypothesis names. They live in `mdata` attached to
each conjunct of the reified context (`Iris.ProofMode.mkNameAnnotation`), and
the `simp` that `step` runs to eliminate `qimp_spec` rebuilds the term and drops
it — after which `istart` sees an unnamed `∗`-chain and moves the whole thing
into a wand.

Recovering them does not need re-introducing anything one by one. `mdata` is
transparent to definitional equality, so the *old* annotated context can simply
be put back — provided it is still defeq to the new one, which it is whenever
the pure fact was eliminated. When it is not, the tactic leaves the goal alone.

The goal is rebuilt as `Entails'`, not `Entails`: `istart` on a plain entailment
never re-parses the left-hand side, it always starts from an *empty* context and
moves the whole thing into a wand (`startProofMode`, `hyps := .mkEmp bi`). The
names only survive while the goal stays in proof-mode form. -/
elab "istep" args:Aeneas.Step.stepArgs : tactic => do
  /- The reified context, with its name annotations, before anything runs. -/
  let saved ← do
    let ty ← instantiateMVars (← (← getMainGoal).getType)
    if ty.isAppOfArity ``Iris.ProofMode.Entails' 4 then pure (some ty) else pure none
  evalTactic (← `(tactic| istep_core $args))
  let some origTy := saved | return
  /- `@Entails' prop bi e goal`, partially applied: reused to rebuild the same
  proof-mode goal around a new right-hand side. -/
  let mkPM := origTy.appFn!.appFn!
  let old := origTy.appFn!.appArg!
  let gs ← getUnsolvedGoals
  let mut gs' := #[]
  for g in gs do
    let ty ← g.withContext do instantiateMVars (← g.getType)
    /- `Entails P W`: put the annotated `P` back if the two agree. -/

    if ← g.withContext do
        pure (ty.isAppOfArity ``Iris.BI.BIBase.Entails 4) <&&> isDefEq ty.appFn!.appArg! old then
      let ty' := (mkPM.app old).app ty.appArg!
      gs' := gs'.push (← g.replaceTargetDefEq ty')
    else
      gs' := gs'.push g
  replaceMainGoal gs'.toList

/-! ## Notation

iris-lean already has the notation, and one of its postcondition brackets is
already Aeneas': `⦃ ⦄`.

```lean
class Wp (PROP Expr : Type _) (Val : outParam (Type _)) (A : Type _) where
  wp : A → CoPset → Expr → (Val → PROP) → PROP

syntax wpExpr := term:max (" @ " term:max (" ; " term:max) <|> …)
syntax " ⦃ " wpPostcondInner " ⦄ " : wpPostcond
```

Instantiating `Wp` with the handler in the parameter slot gives

```
WP t @ H ; M ⦃ v, Q ⦄
```

which is the Coq development's `WPi t @ H ; M {{ v, Q }}` with Aeneas'
brackets, and the whole judgment is `P ⊢ WP t @ H ; M ⦃ v, Q ⦄`.

Two things this settles. The leading `WP ` keyword is what makes it parse:
without it `t @ H` is ambiguous with Lean's explicit-application `@f`, which no
amount of precedence tuning fixes. And the handler is written rather than taken
from an ambient instance — the Coq development writes it too, and hiding it
behind a class field breaks the `-<ₕ` search the rules depend on, since instance
resolution is keyed on head symbols and stops matching through a projection. -/

instance {hlc : Iris.HasLC} {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF] {α : Type} :
    Iris.Wp (IProp GF) (Result α) α (Handler RustEffect GF) where
  wp H M t Φ := wpi_mask GF H t Φ M

/-- Normalise the `lat` wrapper away.

`lat` is a plain `def`, so neither `inext` (which synthesises `FromModal` on the
goal's head) nor `isplitl` (which synthesises `FromSep`) can see through it.
Needs the modality to be concrete — which it always is, since a proof is either
about partial correctness or about total correctness, never both. -/
macro "ilat" : tactic =>
  `(tactic| simp only [AeneasIris.Step.lat_identity, AeneasIris.Step.lat_later])

/-- Expose the leading operation of a `do` block.

The head has to be given: splitting `bind a f` into `?t >>= ?k` is a
higher-order problem, and `iapply` unifies at reducible transparency, where it
cannot guess `?k`. Everything else is inferred. -/
macro "ibind " op:term : tactic =>
  `(tactic| iapply (wpi_bind_result $op _ _ _))

/-- Apply a handler rule to the leading operation of a `do` block, paying for
its precondition with `h`.

Leaves one goal — the continuation — with the resource the rule returns still to
be introduced. Everything the rule did not consume stays in the context
untouched: the frame is never named, computed or threaded, which is the whole
reason the heap rules are applied here rather than registered with `step`.

The `inext` is what makes recursion work: it introduces the `▷` the rule asks
for *and* strips one off every context hypothesis that has one, including a Löb
hypothesis. -/
macro "iheap " op:term " with " rule:pmTerm " using " h:ident : tactic =>
  `(tactic| (ibind $op;
             iapply $rule;
             (first | ilat | skip);
             (first | inext | skip);
             isplitl [$h];
             · iexact $h))

/-- `iheap` in tail position, where there is no bind to peel. -/
macro "iheap! " rule:pmTerm " using " h:ident : tactic =>
  `(tactic| (iapply $rule;
             (first | ilat | skip);
             (first | inext | skip);
             isplitl [$h];
             · iexact $h))

end AeneasIris
