import LtStatefulOptimizerHostile

/-!
# Stateful effects must survive the micro-pass pipeline

The `A → Result B` contract is not only about expressiveness — it is what keeps
Aeneas' own optimizer from eating the effects.

Under the `Result (A → B)` encoding a release is emitted as
`let () := release_fn guard`: a **non-monadic** let binding an unused `()` to a
**pure** application.  That is precisely the pattern
`PureMicroPassesGeneral.filter_useless` deletes (`all_dummies && not monadic`),
that `unit_vars_to_unit` rewrites away, and that `simplify_duplicate_calls` may
merge.  The only way the current implementation keeps such releases alive is by
disabling those passes globally whenever `-stateful-lifetimes` is set.

Under `A → Result B` the release is `let () ← release_fn guard`: monadic, and
`texpr_cannot_fail` is `false` for a function application, so `filter_useless`
takes the `dont_filter` branch and leaves it alone.  The passes can therefore be
re-enabled, and these assertions are what proves it — every one of them fails if
an acquisition or a release is deleted, duplicated, hoisted, sunk or merged.
-/

open Aeneas Aeneas.Std Result ControlFlow
open lt_stateful_optimizer_hostile

/- The generated definitions are noncomputable (they rest on axioms). -/
noncomputable section

namespace LtStatefulOptimizerCheck

/-! ## `filter_useless` must not delete a release whose `()` is unused -/

/-- The release binds nothing anyone reads, and the function continues
afterwards. It must still be there. -/
example :
    release_result_unused =
      (fun (lock : Lock Std.I32) => do
        let (guard, release) ← Lock.read lock
        let _ ← ReadGuard.get guard
        release guard
        ok 7#i32) := by
  rfl

/-- Same, with a write-back first: the release must receive the guard as
updated by the setter and the outer reborrow, not the original one. -/
example :
    release_after_write_unused =
      (fun (lock : Lock Std.I32) => do
        let (guard, release) ← Lock.write lock
        let (_, set, outer) ← WriteGuard.get_mut guard
        let guard ← set 5#i32
        let guard ← outer guard
        release guard
        ok 0#i32) := by
  rfl

/-! ## `simplify_duplicate_calls` must not merge two acquisitions -/

/-- Two syntactically identical `Lock.read lock` calls. Acquisition is an
effect, so common-subexpression elimination would halve the number of times the
lock is taken. -/
example :
    acquire_same_lock_twice =
      (fun (lock : Lock Std.I32) => do
        let (guard, release) ← Lock.read lock
        let first ← ReadGuard.get guard
        release guard
        let (guard1, release1) ← Lock.read lock
        let second ← ReadGuard.get guard1
        release1 guard1
        first + second) := by
  rfl

/-- Two identical acquisitions *and* two identical setter applications on the
same lock — the worst case for CSE. Everything must be duplicated. -/
example :
    write_same_constant_twice =
      (fun (lock : Lock Std.I32) => do
        let (guard, release) ← Lock.write lock
        let (_, set, outer) ← WriteGuard.get_mut guard
        let guard ← set 1#i32
        let guard ← outer guard
        release guard
        let (guard1, release1) ← Lock.write lock
        let (_, set1, outer1) ← WriteGuard.get_mut guard1
        let guard1 ← set1 1#i32
        let guard1 ← outer1 guard1
        release1 guard1) := by
  rfl

/-! ## `unit_vars_to_unit` must not erase a unit-payload write-back -/

/-- Every value flowing through this guard is `()`, so a pass that rewrites
unit binders must still leave the setter, the reborrow and the release. -/
example :
    write_unit_payload =
      (fun (lock : Lock Unit) => do
        let (guard, release) ← Lock.write lock
        let (_, set, outer) ← WriteGuard.get_mut guard
        let guard ← set ()
        let guard ← outer guard
        release guard) := by
  rfl

/-! ## Conditionality: effects behind a branch stay behind it -/

/-- The lock is taken only on the `then` path. -/
example :
    conditional_acquire =
      (fun (lock : Lock Std.I32) (take : Bool) =>
        if take
        then do
          let (guard, release) ← Lock.read lock
          let i ← ReadGuard.get guard
          release guard
          ok i
        else ok 0#i32) := by
  rfl

/-- The two branches acquire different locks and must not be merged. -/
example :
    branch_acquires_different_locks =
      (fun (first second : Lock Std.I32) (useFirst : Bool) =>
        if useFirst
        then do
          let (guard, release) ← Lock.read first
          let i ← ReadGuard.get guard
          release guard
          ok i
        else do
          let (guard, release) ← Lock.read second
          let i ← ReadGuard.get guard
          release guard
          ok i) := by
  rfl

/-! ## Multiplicity: effects inside a loop run once per iteration -/

/-- The acquisition and the release both stay in the loop body; neither is
hoisted into the enclosing function. -/
example :
    acquire_in_loop_loop.body =
      (fun (lock : Lock Std.I32) (count total index : Std.U32) =>
        if index < count
        then do
          let (guard, release) ← Lock.read lock
          let _ ← ReadGuard.get guard
          let total1 ← total + 1#u32
          let index1 ← index + 1#u32
          release guard
          ok (cont (total1, index1))
        else ok (done total)) := by
  rfl

/-! ## Ordering: releases follow Rust drop order -/

/-- Three guards acquired first/second/third are released third/second/first. -/
example :
    three_nested_guards =
      (fun (first second third : Lock Std.I32) => do
        let (firstGuard, firstRelease) ← Lock.read first
        let (secondGuard, secondRelease) ← Lock.read second
        let (thirdGuard, thirdRelease) ← Lock.read third
        let i ← ReadGuard.get firstGuard
        let i1 ← ReadGuard.get secondGuard
        let i2 ← i + i1
        let i3 ← ReadGuard.get thirdGuard
        let i4 ← i2 + i3
        thirdRelease thirdGuard
        secondRelease secondGuard
        firstRelease firstGuard
        ok i4) := by
  rfl

/-- An inner scope closing while an outer guard is held: the inner release is
sequenced strictly between the outer acquisition and the outer release, and does
not sink to the end of the function. -/
example :
    inner_scope_releases_first =
      (fun (outer inner : Lock Std.I32) => do
        let (outerGuard, outerRelease) ← Lock.read outer
        let (innerGuard, innerRelease) ← Lock.read inner
        let _ ← ReadGuard.get innerGuard
        innerRelease innerGuard
        let i ← ReadGuard.get outerGuard
        outerRelease outerGuard
        ok i) := by
  rfl

end LtStatefulOptimizerCheck

end
