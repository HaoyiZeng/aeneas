import AeneasIris.Tactics.Core
import AeneasIris.Rust

/-!
# Regression tests for `istep`

This file began as evidence of a bug and is kept as the guard against its
return. **The bug is fixed**; what follows is the test that would have caught it.

## The bug

```lean
theorem silentSorry_repro (P Q : IProp GF) : P ⊢ Q := by
  istep
```

used to compile with **no error**. `istep`, applied to a goal it had no business
proving, *consumed* the goal instead of failing; the metavariable was left
unassigned and Lean turned it into `sorryAx`. The stronger form `P ⊢ False` was
accepted too, so this was a soundness bug and not merely an over-eager tactic.

It was confined to goals that are **not** `wpi_mask` — an ordinary entailment, a
wand, anything. That mattered because `emp -∗ <wp>` is not a `wpi_mask`, and
that is exactly the shape `ihave … $$ …` leaves behind, which is how it was hit
in practice.

## Retraction, kept on the record

An earlier report called the bug *silent*. That was wrong. Lean did emit
`declaration uses 'sorry'`; a `lake build` showed it and `#print axioms` caught
it. The mis-report came from reading a `grep error` view of the build output and
concluding "no diagnostics" from "no *errors*" — which is a good reason to grep
for `warning` too, and a better reason to check `#print axioms` on anything that
matters.

## Current behaviour

`istep` now raises an error on all three shapes below. One observation worth
passing on: for a goal like `P ⊢ Q` the message reads

> istep: the goal is a `wpi_mask` but the proof-mode context is stale, so no
> rule can fire.

but `P ⊢ Q` is **not** a `wpi_mask`, so that diagnosis is wrong for this case —
the behaviour is right and the explanation is not. Someone chasing a genuinely
stale proof-mode context could be sent looking for a `have`/`rcases` that is not
there. Worth a second branch in the error path.

## Why the tests are shaped the way they are

Each test states a goal that **is** provable, asserts `istep` declines it, and
closes it honestly. So this file contains no `sorry`, defines no constants, and
is safe to import — unlike its two predecessors, one of which left `sorryAx`
around and the other of which put `theorem`s of type `P ⊢ Q` into the
environment, from which any importer could derive `False`.
-/

namespace AeneasIris.Semantics.TacticIssue

open Iris BI Aeneas.Data.Coinductive
open AeneasIris AeneasIris.Heap
open Aeneas.Std (Result RustEffect)

unseal Aeneas.Std.Result

section

variable {hlc : Iris.HasLC} {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]
variable [HeapGS.{0} GF]

/-! ## The regression tests

Each test states a goal that **is** provable, asserts that `istep` refuses it,
and then closes it honestly. This is a deliberate improvement over the earlier
form of this file, in three ways:

* **No `sorry`, no `sorryAx`, nothing tainted.** The earlier version had to
  leave the goals open, because the whole point was that `istep` "proved" them.
* **No named constants.** An even earlier version stated them as `theorem`s,
  putting constants of type `P ⊢ Q` for arbitrary `P`, `Q` into the environment —
  a single stray `import` would have yielded `False`.
* **No message matching.** Asserting the exact error text would break every time
  the message is reworded, and the text is not what matters. What matters is
  that `istep` *fails* rather than silently succeeding. `fail_if_success`
  says exactly that and nothing more.
-/

/-- An ordinary BI entailment is not a `wpi_mask`; `istep` must decline it. -/
example (P : IProp GF) : P ⊢ P := by
  fail_if_success istep
  exact .rfl

/-- The same, for a goal `istep` might plausibly mistake for something it can
discharge. -/
example (P : IProp GF) : P ⊢ iprop(True) := by
  fail_if_success istep
  exact BI.true_intro

/-- **The shape that caused the original bug.** `ihave … $$ …` leaves the
continuation as `emp -∗ <goal>`, and a wand is not a `wpi_mask`. This is the
test that would have caught it. -/
example (P : IProp GF) : P ⊢ iprop(emp -∗ P) := by
  iintro HP
  /- The goal is now `emp -∗ P`, exactly what `ihave … $$ …` leaves behind. -/
  fail_if_success istep
  iintro _
  iexact HP

/-! ## `ihave` was never implicated

It leaves the continuation goal exactly where it should be, and it is closeable.
Recorded because the bug first showed up in an `ihave` proof and the assertion
tactic was the natural first suspect. -/

example : (iprop(emp) : IProp GF) ⊢ iprop(True) := by
  ihave Ht : iprop(True) $$ []
  · itrivial
  /- The continuation goal is still here, as it should be. -/
  iintro _
  itrivial

end

end AeneasIris.Semantics.TacticIssue
