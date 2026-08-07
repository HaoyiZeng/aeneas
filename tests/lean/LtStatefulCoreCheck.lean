import LtStatefulCore

/-!
# Generated sequencing for stateful lifetimes, pinned by `rfl`

`LtStatefulContractCheck` pins the *types*; this file pins the *bodies*, which
is where the two encodings differ observably.

The wrong encoding generates
```
let stateful_back1 ← stateful_back     -- effect discharged here
let () := stateful_back1 guard         -- guard supplied here, purely
```
and the right one generates
```
release guard                          -- effect discharged with the guard
```

Beyond the shape, these assertions pin three properties that the release must
have and that no type can express:

* **position** — the release happens where the Rust guard is dropped, not
  earlier or later;
* **argument** — the release receives the *final* value of the guard, after
  every write has been folded back into it;
* **order** — guards are released in reverse acquisition order, matching Rust
  drop order.
-/

open Aeneas Aeneas.Std Result
open lt_stateful_core

/- The generated definitions are noncomputable (they rest on axioms). -/
noncomputable section

namespace LtStatefulCoreCheck

/-- A write through a method call.

The release takes the guard *after* both `set` (the payload write-back) and
`outer` (the end of the reborrow) have updated it, and it is the last effect of
the function. -/
example :
    write_method =
      (fun (lock : Lock Cell) => do
        let (guard, release) ← Lock.write lock
        let (cell, set, outer) ← WriteGuard.get_mut guard
        let cell ← Cell.set cell 42#i32
        let guard ← set cell
        let guard ← outer guard
        release guard) := by
  rfl

/-- A read guard whose lexical scope ends before a second lock is acquired.

The read release must be sequenced *before* `Lock.write`, otherwise the model
would allow holding both locks at once. -/
example :
    scoped_read_then_write =
      (fun (readLock writeLock : Lock Std.I32) => do
        let (readGuard, readRelease) ← Lock.read readLock
        let _ ← ReadGuard.get readGuard
        readRelease readGuard
        let (writeGuard, writeRelease) ← Lock.write writeLock
        writeRelease writeGuard) := by
  rfl

/-- Two guards held simultaneously, released in reverse acquisition order.

`second` is acquired last and released first.  Each release receives its own
final guard value, so the guard/lock pairing is visible in the generated term —
the property `LtStatefulEffectCheck.old_shape_pairing_unenforced` shows the old
encoding cannot express. -/
example :
    write_two =
      (fun (first second : Lock Std.I32) => do
        let (firstGuard, firstRelease) ← Lock.write first
        let (secondGuard, secondRelease) ← Lock.write second
        let (_, firstSet, firstOuter) ← WriteGuard.get_mut firstGuard
        let firstGuard ← firstSet 1#i32
        let (_, secondSet, secondOuter) ← WriteGuard.get_mut secondGuard
        let secondGuard ← secondSet 2#i32
        let secondGuard ← secondOuter secondGuard
        secondRelease secondGuard
        let firstGuard ← firstOuter firstGuard
        firstRelease firstGuard) := by
  rfl

/-- A release that is *not* in tail position: the function keeps computing
afterwards.  This is the shape that `filter_useless` deletes when the release is
a pure application, because the `()` it binds is unused. -/
example :
    update_external_and_lock =
      (fun (_value : Std.I32) (lock : Lock Std.I32) => do
        let (guard, release) ← Lock.write lock
        let (_, set, outer) ← WriteGuard.get_mut guard
        let guard ← set 7#i32
        let guard ← outer guard
        release guard
        ok 99#i32) := by
  rfl

/-- Zero-input stateful backward functions: `refresh`'s write-back has no input
so it is evaluated by the callee and the refreshed guard is returned directly,
while its release, having no output, stays suspended and is run here. -/
example :
    refresh_one =
      (fun (lock : Lock Std.I32) => do
        let (guard, release) ← Lock.read lock
        let (guard, refreshRelease) ← ReadGuard.refresh guard
        refreshRelease
        let _ ← ReadGuard.get guard
        release guard) := by
  rfl

end LtStatefulCoreCheck

end
