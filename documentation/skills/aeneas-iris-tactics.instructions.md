---
name: aeneas-iris-tactics
description: Tactics, registry, and pitfalls for the Iris program logic on Aeneas' ITree backend (backends/lean-iris)
---

# Aeneas + Iris Tactics — Skill File

This covers `backends/lean-iris`, the "program logics à la carte" development:
an Iris program logic over Aeneas' `ITree`, with `wpi_mask` as the weakest
precondition and a `step`-style automation layer on top.

It is **not** about the pure-Lean Aeneas backend. For that see
`aeneas-tactics-quickref`. The two share the name `step` and nothing else.

## The judgment

There is exactly **one** Hoare-triple judgment:

```lean
def iSpec {E : Effect} {α : Type} (H : Handler E GF) (P : IProp GF)
    (t : ITree E α) (Φ : Post GF α) (M : CoPset) : Prop :=
  P ⊢ wpi_mask GF H t Φ M
```

written `⦃ P ⦄ (t) @ H ; M ⦃ v, Q ⦄`. The notation expands **to the entailment**,
not to `iSpec` — definitionally equal, so the registry still reads the program
off the conclusion, but `iintro` works on it directly with no `@[reducible]`.

⛔ Do **not** mark `iSpec` `@[reducible]` to make `istart` see through it. It
changes how *applications* elaborate elsewhere and breaks `ArcLAT` (`ITree
RustEffect α` stops unifying with `Result α`).

**Specs carry no modality.** No `▷` and no continuation-passing appear in a
registered rule; both are the tactic's business. `wpi_stepThen'` is literally
`step_spec` continuationised — `Triple.lean` derives one from the other, so the
step branch of `irule` is not a second rule but the same one applied differently.

## Tactic reference

| Tactic | Does |
|---|---|
| `istep` | One machine step: `irule`, else a pure Aeneas call, else `iret` |
| `irule` | Apply a registered rule, paying its precondition by framing |
| `irule with thm` | Same, but naming the rule — skips the registry and the search |
| `ibind` | Expose the leading operation of a `do` block |
| `iret` | Hand a returned value to the postcondition |
| `iunfold X (at H)?` | Proof-mode `unfold` |
| `ilat` / `inext` | Reduce `lat m` to the concrete modality, then strip `▷` |
| `iaupd_commit`/`iaupd_abort` | Open a logically atomic update (see below) |

**`istep` tries `irule` first, and the order matters.** `istep_core` (Aeneas'
pure-call replay) is very slow to *fail* in a large proof-mode context — on a
`cas` under an open atomic update it exhausts the entire heartbeat budget — and
it can never apply to an operation that has a registered rule.

## The registry

Tag a rule with `@[istep_rule]`. The operation it is about is read off its own
conclusion; nothing is written down twice.

```lean
structure Info where
  rule      : Name
  nExplicit : Nat
  style     : Style := .triple   -- `.triple` | `.cont`
  mintsLat  : Bool  := false     -- read off the rule's binders
```

`Style` is about **the shape the rule is stated in**, which decides how its
precondition is discharged:

| | the precondition is | determined by | discharged by |
|---|---|---|---|
| `triple` | a resource, `l ↦ v` | unifying the rule's program with the goal | framing it out of the context |
| `cont` | the rest of the weakest precondition | the goal's *continuation*, by unification | the goal itself |

Write `@[istep_rule cont]` for the second. `mintsLat` is not declared — it is
read off the rule's binders, because minting a modality is a property of the
rule and not of the style.

**Why `stepP` is registered `cont` and not as a triple.** The triple
`∀ P, ⦃ lat m P ⦄ stepP ⦃ _, P ⦄` is true (`Triple.step_spec`), but `P` is not
determined by the goal, so framing has nothing to match:

```
iframe: cannot solve Step.lat ?m ?P by framing
```

`P := emp` *is* frame-directed and gives a sound but useless rule — the step is
taken and the `▷` discarded, so `inext` never runs and Löb induction is lost.
The instantiation that works is `P := wpi_mask … (k ()) Φ M`, read off the goal,
which is exactly `wpi_stepThen'`.

Several rules may be registered per operation (`cas` has success and failure).
`irule` sweeps them in **three passes**: named candidates, then framing over the
whole context, then `itrivial`. Within one rule the order would be wrong — on the
failing branch `cas_succ`'s autoframe runs before `cas_fail` is ever reached.

## Masks: one rule

> **`⊤` iff it contains a `yield`. Everything else is mask-polymorphic.**

`wpi_open_invariant` and `wpi_clear_mask` carry **no** `Atomic` side condition
(every event in an ITree is one node), so an invariant may be held open across
arbitrarily many events. The only thing that closes the window is a yield, which
demands `⊤`.

So in this logic **"atomic" means "yield-free", not "one step"**. A `stepP` may
sit inside an atomicity window; a `yield` may not.

⊤-only: `wpi_yield`/`yieldU_spec`, `sync_spec`, `wpi_kill`, `load_na_spec` and
`store_na_spec` (a non-atomic access *contains* a yield — that is what makes it
non-atomic), `join_spec`, and the *new thread* premise of `wpi_fork`.

### Where the step and the yield go

Per event: **`yield; step; body`**.

- **step before the body**, so its `▷` is available *at* the operation. Open an
  invariant, then spend the step, and `inext` strips the invariant's `▷` along
  with the goal's. Step-after is strictly weaker — you would need timelessness.
- **yield before the step**, never between step and body: an invariant must not
  be held across a scheduling point.
- **Do not yield at thread-private events.** Insert a yield where another thread
  could observe, i.e. at shared-memory operations. A yield at a private access
  costs `⊤` for no soundness gain.

⚠️ `istep` spends the modality eagerly (`wpi_stepThen'; ilat; inext` in one go),
so **open the invariant or the atomic update *before* `istep`**, not after.

## Logically atomic triples

`wpi_clear_mask.mp` turns the goal into a **fupd** wrapping a `wpi_mask`, and
`Read.wpGoal?` recognises only `wpi_mask` and `Iris.Wp.wp` — so `istep` cannot
run there. Use the packaged lemmas instead; they keep the goal a `wpi_mask`
throughout:

```lean
theorem wpi_aupd_commit (t) (α β Ψ) (Φ) :
    atomicUpdate ⊤ ∅ α β Ψ ⊢
      ((∀ x, α x -∗ wpi_mask GF Hd t (fun v => ∃ y, β x y ∗ (Ψ x y -∗ Φ v)) ∅) -∗
       wpi_mask GF Hd t Φ ⊤)
```

Stated **curried**, `AU ⊢ (body -∗ goal)`, for the same reason as
`iSpec.apply`: `iapply` reads the `⊢` as a leading wand, so `iapply … $$ HAU`
hands the update over. A single `∗` premise would need an `isplitl` at every use.

The client-facing form is a tactic, arity-generic:

```lean
iaupd_commit HAU as ⟨s, v⟩ with Hlock
```

`as` takes an **`rcasesPat`**, so `⟨a⟩`, `⟨s, v⟩`, `⟨a, b, c⟩` all work. The
`⟪ ∀ x y … ⟫` notation packs its binders through `auUncurry`; splitting the
packed variable is what an `rcases` pattern does at any arity, and after the
split `auUncurry p (s, v)` reduces (`auUncurry_pair`, a `@[simp]` `rfl`) so
`auUncurry` never appears in the goal.

⛔ Do **not** write a family of lemmas indexed by the number of binders. The
general lemma is already arity-generic — only *reading* the packed binder is not,
and that belongs in a tactic.

`oneShotUpd` is the one-attempt form (no abort branch, no greatest fixpoint),
with `wpi_oneShot_commit` alongside.

## Pitfalls

Each of these cost a debug round. They are all cheap to hit again.

### Elaboration and scoping

1. **The `Mode` is written in the statement; no `include m` is needed.** A
   mode-generic spec reads

   ```lean
   variable {m : Mode} {Hd : Handler E GF} [stepH GF m -<ₕ Hd]
   theorem foo : ⦃P⦄ t @ Hd ; m ; M ⦃v, Q⦄
   ```

   `m` is an argument of `wpi_mask`, so it occurs in the conclusion and is
   auto-included along with the `stepH` instance.

   This is worth knowing because it used *not* to be so: when the mode was a
   field of `Handler`, `m` lived only inside the instance binder, was not
   auto-included, and its absence left `istep` with no step handler to find —
   burning the whole heartbeat budget in instance search and failing with what
   looked like a framing timeout. If you meet that symptom in old code or a
   stale branch, this is it.

   **Do not reintroduce a second place to write the mode.** It has two consumers
   — `lat` (via `stepH`, on `vis`) and `divOK` (on `div`) — and they agree only
   because they name the same variable. A field on `Handler` or a type class
   indexed by it splits them: `-<ₕ` constrains `run` and nothing else, so
   `stepH GF .total -<ₕ Hd` with the wp read at `.part` becomes writable.
   Coherence belongs in the adequacy theorem, which demands the matching step
   summand, not in a class on every declaration.

1b. **`WP` pairs the handler with the mode: `WP t @ (H, m) ; M ⦃v, Q⦄`.**
   `Iris.Wp` offers a single parameter slot and `wpi_mask` needs both, so the
   instance is at `Handler RustEffect GF × Mode`. The pair exists only at that
   notation boundary — every rule takes `H` and `m` separately, so no `-<ₕ`
   constraint is ever stated about a projection. The triple notation has its own
   slot instead: `⦃P⦄ t @ H ; m ; M ⦃v, Q⦄`.

   A literal mode inside the pair needs qualifying (`(RH GF, Mode.part)`): there
   is no expected type there to resolve `.part` against, and `Mathlib.Tactic.Order`
   also has a `part`.
2. **`open scoped Aeneas.Std`** for `DecidableEq Val` and `Decidable (v.1 = T)`.
   They are deliberately `scoped` classical instances (a global one would silently
   make unrelated definitions `noncomputable`). Comparing two `Val`s compares
   their *types* first, which is why they must be classical at all.
3. **`omit`/`include` must precede the doc comment**, not sit between it and the
   declaration.
4. **An attribute cannot be used in the file that defines it.** `@[istep_rule]`
   on `wpi_stepThen'` lives in `Tactics.lean`, not in `Triple.lean`.

### Tactic behaviour

5. **`$$ [h]` is not "autoframe picking `h`".** `[$]` *proves* the precondition
   by framing; `[h]` only *assigns* `h` to it and leaves `h ⊢ P` open. Close it
   (`iexact h`). Both leave the rest of the context to the continuation.
6. **`ibind` needs the general `wpi_bind` for non-`Result` programs.** A program
   written generically in the effect row and instantiated —
   `RwLock.try_write (E := RustEffect)` — has type `ITree RustEffect _`, and
   `Result` is a `def`, so `wpi_bind_result` does not match at reducible
   transparency.
6b. **⚠️ A `have` between proof-mode steps invalidates the reified context.** This is the
   single most expensive trap found so far. After a `have`, `irule`/`ibind` report
   **"the goal is not a `wpi_mask`"** on a goal that *prints* as a perfectly good
   `wpi_mask`.

   **Fix: hoist every `have` above the opening `iintro`.** Nothing else changes.

   `istep` now detects this and says so directly ("the proof-mode context is stale"),
   so you should not have to diagnose it by hand. Historically it did not: `istep`
   discarded the `irule` failure and fell through to `istep_core`, which burned the
   whole heartbeat budget, so the symptom was a **deterministic timeout** and the two
   natural diagnoses — "decompose the proof" and "raise `maxHeartbeats`" — were both
   wrong. If you ever see that timeout shape from `istep` again, suspect a stale
   context first. Note the detection must run *before* the fallback: once heartbeats
   are exhausted, `throwError` can no longer render its own message.

   `rcases`, `cases`, `split` and `rw` corrupt the reified context the same way — after
   them, hypotheses print with raw fvar ids like `_fvar.187724.2910`. Do the destructuring
   *inside* the proof-mode tactic instead, e.g.
   `obtain ⟨(_ | k | _), v⟩ := iaupdPacked` rather than `obtain` followed by `cases`.
   `simp only` is safe.

6c. **`rw [atomicWpi]` beats `simp only [atomicWpi]` at the top of an atomic spec.** `rw`
   unfolds only the outer triple and leaves a nested release box folded, so the goal stays
   small and a folded helper lemma still matches it with no `simp` at all. `simp only`
   unfolds the nested box too, which is what forces you into the
   `have H := lemma; simp only [atomicWpi] at H; iapply H` dance.

7. **`simp only [...] at H` does not work on proof-mode hypotheses.** Use
   `iunfold X at H`, or plain `simp only [...]` — it traverses the reified
   context as well as the goal.
8. **`reduceIte` does not fire on `if True`.** `simp` rewrites
   `LockState.free = LockState.free` to `True` first, and then `reduceIte` is
   stuck; use `if_true`. It also does not handle `if (false : Bool) = true` at
   all — even outside proof mode — so use `Bool.false_eq_true` first. Between
   them these explain every "manual ite" in the LAT proofs; `reduceIte` itself
   works fine in proof mode, in the goal and under binders in hypotheses.
9. **`iapply` unifies at reducible transparency.** A `Decidable` instance that
   does not reduce there blocks it; rewrite the `ite` away first.
9a. **The three ways an `ite` resists rewriting in proof mode.** Try them in this order:
   1. *The equation never fires.* A `have hif : (if c then a else b) = b` pins a
      `Decidable` instance that differs from the program's. Use **`if_neg h` / `if_pos h`**
      instead — their instance is a *variable*, so it unifies with anything.
   2. *Even that is awkward.* Rewrite the **condition** to `False`/`True` and let
      `if_false`/`if_true` fire, **in the same `simp only` call**:
      `simp only [eq_false hnn, if_false]` or `simp only [lt_self_iff_false, if_false]`.
      `simp only [if_true]` alone is not enough, because simp rewrites `C = C` to `True`
      first and then `reduceIte` is stuck (pitfall 8).
   3. *The scrutinee is unreachable* — `rw` reports the pattern absent and `simp only`
      no progress, even though `pp.explicit` shows the term verbatim (`kabstract` cannot
      enter the reified goal). Then **lift the equation to the whole `IProp`**, with a
      *closed* left-hand side, generalised over any bound variable:
      ```lean
      have hEq : isRwLock γ lk (if s = .free then .write else s) v = isRwLock γ lk s v := by
        rw [show (if s = LockState.free then LockState.write else s) = s from if_neg hs]
      simp only [hEq]
      ```
      If the `ite` sits under a binder (a `RET` binder, or `auUncurry`), generalise:
      `have hite : ∀ z, (if c then f z else g) = g := fun _ => if_neg h`.
      The left-hand side must use the **same syntactic form the goal has** after your
      earlier `simp only`s (`⟨lk⟩` vs `mkWriteGuard lk` — defeq is not enough).
   4. Never `subst` a variable bound by an atomic update: `subst` turns `n = 0` into
      `0 = 0`, simp's `eqSelf` turns that into `True`, and the transported `Decidable`
      instance then blocks every rewrite *and* defeq.

9b. **An `ite` on an abstract scrutinee can be unrewritable — `cases` it.**
   Symptom: the goal visibly contains `if s = C then a else b`, `hs : ¬ s = C`
   is in scope, and *all three* of `simp only [if_neg hs]`, `rw [if_neg hs]` and
   `split` report no progress / pattern absent / no `ite` found.

   Cause: the instance in the goal is the `scoped` classical one from
   `open scoped Aeneas.Std`, not the `DecidableEq` derived on the type, so a
   rewrite keyed on the latter never matches. All three tactics locate `ite`s by
   the instance, so all three miss it together — which is the tell.

   Fix: `cases s` instead of rewriting. Each branch puts a *constructor* in the
   scrutinee, so the `ite` reduces by iota before any tactic looks at it, and
   `iexact` closes the branch up to defeq. The impossible branch is
   `exact absurd rfl hs`. Do not reach for `decide`, `simp [reduceIte]` or a
   `Decidable` instance annotation — after `cases` there is nothing left to
   simplify, and a `simp` there errors with "made no progress".

### Writing tactics

10. **Syntax categories bite.** `$$` takes `specPat`; `icases`/`imod` take
    `pmTerm`; `$$ [h]` takes `frameIdent`; `%x` and bare names in `icasesPat` are
    over **`binderIdent`**, not `ident` — a spliced `ident` prints identically and
    is rejected. Build them through quotation (`` `(frameIdent| $id:ident) ``),
    never by re-tagging a `TSyntax`.
11. **`ihave X := term $$ args` needs `term`'s type to be determined.** Inside a
    macro it often is not, and the error is `ihave: ?m is not a Prop`. If the same
    text works inline and not in a macro, this is why. The fix is not to fight the
    macro: package the step as a **lemma** first, and then the macro body is just
    `iapply <named lemma>` with nothing to infer.
12. **`||` is overloaded** by `Iris.Instances.Data` at a precedence that swallows
    `==`. Use two `if`s.
13. **Mutable `do` variables cannot be shadowed** by `let` of the same name.

### Hard rules

14. ⛔ **Never raise `maxHeartbeats` to make something pass.** Every timeout in
    this development so far had a real cause — a missing `include`, a missing
    scoped instance, a tactic ordering — and raising the limit would have hidden
    all of them.
15. ⛔ **Never `lake clean` or delete `.lake/`.**
16. **Use `lake env lean <file>` for single-file checks — but never to test a
    change to a *dependency*.** It does not write `.olean`s, so a downstream file
    is checked against the dependency's **stale** `.olean`. This is silent and
    has twice produced a confidently wrong diagnosis here: an attribute change
    (`@[istep_rule cont]`) appeared not to take effect, and a `macro_rules` branch
    appeared not to fire — in both cases the new code was correct and simply was
    not being run. Anything baked into the `.olean` at compile time — **attributes,
    macros, syntax, instances, simp sets** — must be re-checked with `lake build`
    on the *changed* module before testing anything downstream.
17. **A rule that is not imported is not registered.** `irule: no rule is
    registered for X` is usually the literal truth: the `@[istep_rule]` lives in a
    module the current file does not import. `RwLockImpl` imported
    `Effects.Conc` (which has `wpi_sync`) but not `Effects.ConcAPI` (which has
    `sync_spec`), so every `sync` had to be driven by hand — while the manual
    `iapply (Conc.wpi_sync …)` kept working, hiding the cause. **Check the imports
    before suspecting the tactic.**
18. **Register a rule whose premise is the continuation as `@[istep_rule cont]`.**
    A `.triple` rule's precondition is a *resource*, which `irule` pays out of the
    spatial context, finishing with `itrivial`. If the precondition is instead the
    weakest precondition of the rest of the program (`sync_spec`:
    `⦃ wpi_mask … op Q ⊤ ⦄ (sync op) ⦃ v, Q v ⦄`) that is the wrong treatment — it
    must become a new goal. The symptom is
    `ispecialize: itrivial could not solve <the continuation's wp>`.
19. **Splicing an identifier into a `%` intro pattern needs a `binderIdent`.**
    `syntax "%" binderIdent : icasesPat`, but the child of an `rcasesPat.one` is a
    *raw* `ident`.  Splicing it directly gives `Unexpected syntax / failed to
    pretty print term`; wrap it first with `` `(Lean.binderIdent| $id:ident) ``.
20. **`obtain x := v` on a bare local variable is a no-op.** The name is accepted
    and silently dropped, so a tactic that expands to it accepts a binder it never
    binds.  A *tuple* pattern is fine, and is not interchangeable: `obtain ⟨a,b⟩ := v`
    destructures `v` **in place**, substituting into hypotheses already in scope,
    which is usually what the surrounding proof depends on.  So a tactic taking an
    `rcasesPat` must dispatch on its kind rather than picking one expansion.
21. **`mintsLat` is a property of the precondition, not of the argument list.**
    `analyse` decides whether to append a `lat` introduction. Deciding it by
    "does the rule take a `Mode`?" is wrong: a rule can take a `Mode` and still
    have an ordinary precondition, and the spurious `lat` step then makes the
    rule fail. It is read off the precondition's head instead.

## Differential gate

`AeneasIris/Test.lean` exercises both kinds of step (pure Aeneas call and machine
operation) on one goal, with a frame that no step may disturb. **Any change to
`Tactics.lean` must leave its failure set unchanged.** It caught, among others, a
prefilter that silently handed the continuation an empty context.
