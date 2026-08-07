import LtStatefulCore

/-!
# The stateful backward-function contract, pinned at the type level

Every stateful backward function must have the shape

```
A → Result B          -- argument first, effect at application
```

and **not**

```
Result (A → B)        -- effect first, argument later
```

`LtStatefulEffectCheck` proves why: with `Result (A → B)` the effects are fixed
before the argument is known, so a lock release can never name the guard it
releases, and `MultiShot.RwLockAPI.write_spec` becomes uninstantiable.

This file pins that contract against the actual extraction output of
`tests/src/lt-stateful-core.rs`, together with the cases that must *not*
change.  It is a type-level test: each `example` is an ascription that fails to
elaborate if the emitted signature has the wrong shape.
-/

open Aeneas Aeneas.Std Result
open lt_stateful_core

/- The generated definitions are noncomputable (they rest on axioms). -/
noncomputable section

namespace LtStatefulContractCheck

/-! ## Stateful backward functions with at least one input

These are the signatures the `Result (A → B)` encoding gets wrong. -/

/-- `Lock::read` hands back a read guard plus the release for it.  Releasing
consumes the guard and performs an effect, so the release is
`ReadGuard T → Result Unit`. -/
example {T : Type} :
    Lock T → Result (ReadGuard T × (ReadGuard T → Result Unit)) :=
  @Lock.read T

/-- `Lock::write`, same contract with a write guard. -/
example {T : Type} :
    Lock T → Result (WriteGuard T × (WriteGuard T → Result Unit)) :=
  @Lock.write T

/-- `WriteGuard::get_mut` has two stateful groups: the inner setter, which
writes the payload back into the guard, and the outer one, which ends the
reborrow of the guard.  Both are effectful, so both take their argument first
and land in `Result`. -/
example {T : Type} :
    WriteGuard T →
      Result (T × (T → Result (WriteGuard T)) ×
        (WriteGuard T → Result (WriteGuard T))) :=
  @WriteGuard.get_mut T

/-! ## Cases that must NOT change

A stateful backward function with **no input and no output** already has the
right shape: `mk_arrows [] (Result B)` and `Result (mk_arrows [] B)` are the
same type. The fix must leave those signatures byte-identical. -/

/-- `observe` is a *transparent* function carrying a stateful lifetime whose
backward function consumes nothing and produces nothing. It is handed to the
caller as a suspended `Result Unit` and is unchanged by the fix. -/
example : Lock Std.I32 → Result (Std.I32 × (Result Unit)) := observe

/-! ## Zero-input backward functions *with* an output are now evaluated

`ReadGuard::refresh` takes `&mut self`, so it has two stateful groups: the
write-back, which consumes nothing and returns the updated guard, and the
release, which consumes and returns nothing.

The write-back now takes part in the ordinary "merged forward/backward"
simplification (`back_sg_is_evaluated`): having no input, there is nothing to
wait for, so it is evaluated by the callee and the updated guard is returned
directly rather than as a suspended `Result (ReadGuard T)`.

This is the point of the fix — a stateful backward function is an ordinary
effectful one — and it is strictly better than the previous output, which forced
the caller to bind the guard out of a `Result` before it could use it. The
release, having no output, keeps its suspended form. -/
example {T : Type} :
    ReadGuard T → Result (ReadGuard T × (Result Unit)) :=
  @ReadGuard.refresh T

/-! ## Consistency anchor

`choose` returns `&'a mut i32` for a lifetime that is **not** stateful, but its
body calls stateful functions, so Aeneas classifies the backward function as
effectful.  Vanilla Aeneas already emits `A → Result B` for that case — via
`mk_back_output_ty_from_effect_info`, which wraps the *codomain*.

So the correct shape is not a new invention: it is what the existing pipeline
produces whenever it is allowed to.  Pinning `choose` next to `Lock.write`
above makes the discrepancy a build failure rather than a code review issue. -/
example :
    Std.I32 → Lock Std.I32 → Result (Std.I32 × (Std.I32 → Result Std.I32)) :=
  choose

end LtStatefulContractCheck

end
