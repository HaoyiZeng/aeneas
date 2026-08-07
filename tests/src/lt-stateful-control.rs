//@ [!lean] skip
//! EXPECTED AFTER IMPLEMENTATION:
//! This file complements `lt-stateful-signatures.rs` and
//! `lt-stateful-reborrows.rs` and focuses on how an *effectful guard*
//! (acquired from a `Lock` and ended via `release`, standing in for a
//! future `Drop`-driven release) behaves across **control-flow joins**:
//! `if`/`else`, `match`, early `return`, short-circuit boolean operators,
//! `if let`/`while let`, and a guard held across a higher-order callback.
//! Once `#[verify::stateful_lifetimes]` is implemented, the translation is
//! expected to track, for every program point, whether a stateful guard is
//! *still open* (needs a `release`-shaped backward function threaded to
//! that point) or *already closed* (nothing left to thread). At a join
//! point (the merge after an `if`/`match`, or a function return), all
//! incoming branches must agree on this open/closed shape for every live
//! stateful value:
//!   - If every branch ends the guard the same way before the join (e.g.
//!     every branch calls `release()`, or no branch ever touches the lock
//!     at all), the join is trivial and the existing symbolic-context
//!     merge machinery (the same one used for ordinary borrows today)
//!     should handle it unchanged.
//!   - If branches disagree — one releases, another leaks the guard past
//!     the join (e.g. via an early `return` that skips `release()`) — the
//!     shapes cannot be merged. This is exactly the situation the existing
//!     `-strict-joins` flag reports as an error for ordinary borrows today
//!     (`Report an error whenever joining contexts fails rather than
//!     duplicating the code after the branching statement`, see
//!     `-strict-joins` in `src/Main.ml`) rather than silently duplicating
//!     the continuation. Once stateful lifetimes are implemented, the
//!     analogous mismatch for a guard's release obligation should ideally
//!     be surfaced as a dedicated diagnostic rather than accepted silently.
//!
//! **Blanket caveat — failure and unwinding:** every `[SUPPORTED]` tag
//! below implicitly assumes the *normal* (non-failing) execution path.
//! Aeneas's pure translation models a Rust panic (and, more generally, any
//! path that would unwind the stack in a real execution) as `fail`, which
//! short-circuits the surrounding `Result` computation immediately —
//! skipping every statement lexically between the failure point and the
//! function's exit, in particular any `release()` call that would
//! otherwise have run. Concretely: if a branch, arm, or callback
//! invocation in any function below can panic (e.g. an arithmetic
//! overflow, an indexing failure, or the explicit panic branch in
//! `guard_around_panicking_callback`) while a guard is
//! open, the pure semantics leaks that guard on the failing path exactly
//! like an unreleased early `return` does, regardless of how the function
//! is tagged. This caveat is non-vacuous today: several supported fixtures
//! perform overflow-checked arithmetic while a guard is open. The opaque
//! lock methods themselves need not panic for the critical section to
//! contain a failing operation.
//!
//! Each function below is tagged in its doc comment with one of:
//!   - `[SUPPORTED]`: every branch ends (or never opens) the guard
//!     consistently before the join; expected to remain accepted, with
//!     real release-bookkeeping attached once the feature lands.
//!   - `[DIAGNOSTIC CANDIDATE]`: at least one path leaks the guard past a
//!     join (or the function boundary) without releasing it; expected to
//!     eventually be rejected (or explicitly documented as intentionally
//!     permissive) once release-obligations are tracked.
//!   - `[NO-REGRESSION]`: no lock/guard is involved at all; included to
//!     confirm ordinary control-flow-join translation for plain `&mut`
//!     values must remain byte-for-byte unaffected by this feature.
//!
//! CURRENT BASELINE:
//! `#[verify::stateful_lifetimes]` is an inert tool attribute today
//! (registered via `#![register_tool(verify)]` but not yet interpreted by
//! Aeneas). `Lock`, `ReadGuard`, and `WriteGuard` are `#[verify::opaque]`,
//! so every method call on them (`read`, `write`, `try_read`, `try_write`,
//! `get`, `get_mut`, `release`) is extracted today as an ordinary opaque
//! call with no linear/release tracking whatsoever. Every function in this
//! file — including the ones tagged `[DIAGNOSTIC CANDIDATE]` — is expected
//! to compile and extract fine today: nothing currently forces `release()`
//! to be called on every path, since it is just a plain (opaque) method
//! taking `self` by value. This file exists so that, once the feature
//! lands, these shapes can be used (unmodified, or with minimal changes) as
//! regression and diagnostic-acceptance fixtures.
#![feature(register_tool)]
#![register_tool(verify)]

use std::marker::PhantomData;

/// Opaque lock guarding a `T`. See `lt-stateful-signatures.rs` for the
/// rationale behind modeling it as an inert `PhantomData`-backed struct.
#[verify::opaque]
pub struct Lock<T> {
    _marker: PhantomData<T>,
}

/// Opaque read guard, tied to the lifetime of the `Lock` borrow that
/// produced it.
#[verify::opaque]
pub struct ReadGuard<'a, T> {
    _marker: PhantomData<&'a T>,
}

/// Opaque write guard, tied to the lifetime of the `Lock` borrow that
/// produced it.
#[verify::opaque]
pub struct WriteGuard<'a, T> {
    _marker: PhantomData<&'a mut T>,
}

impl<T> Lock<T> {
    #[verify::opaque]
    pub fn new(_value: T) -> Self {
        unimplemented!()
    }

    /// Acquire a read guard. EXPECTED: backward release `ReadGuard -> Result Unit`.
    #[verify::opaque]
    pub fn read(&self) -> ReadGuard<'_, T> {
        unimplemented!()
    }

    /// Acquire a write guard. EXPECTED: backward release `WriteGuard -> Result Unit`.
    #[verify::opaque]
    pub fn write(&self) -> WriteGuard<'_, T> {
        unimplemented!()
    }

    /// Fallible acquire. EXPECTED: same release shape, wrapped in `Option`.
    #[verify::opaque]
    pub fn try_read(&self) -> Option<ReadGuard<'_, T>> {
        unimplemented!()
    }

    /// Fallible acquire. EXPECTED: same release shape, wrapped in `Option`.
    #[verify::opaque]
    pub fn try_write(&self) -> Option<WriteGuard<'_, T>> {
        unimplemented!()
    }
}

impl<'a, T> ReadGuard<'a, T> {
    /// Shared deref through a read guard. EXPECTED: no backward function.
    #[verify::opaque]
    pub fn get(&self) -> &T {
        unimplemented!()
    }

    /// Explicit release, standing in for a guard's future `Drop`. EXPECTED:
    /// this is exactly the `Guard -> Result Unit` backward function the
    /// feature should synthesize automatically once implemented.
    #[verify::opaque]
    pub fn release(self) {}
}

impl<'a, T> WriteGuard<'a, T> {
    /// Shared deref through a write guard. EXPECTED: no backward function.
    #[verify::opaque]
    pub fn get(&self) -> &T {
        unimplemented!()
    }

    /// Mutable deref through a write guard. EXPECTED: exactly one setter
    /// backward function `T -> Result Guard`.
    #[verify::opaque]
    pub fn get_mut(&mut self) -> &mut T {
        unimplemented!()
    }

    /// Explicit release. EXPECTED: `Guard -> Result Unit` backward function.
    #[verify::opaque]
    pub fn release(self) {}
}

/// Plain (non-opaque) struct, used only by the `[NO-REGRESSION]` fixtures
/// at the bottom of the file to exercise ordinary `&mut` control-flow joins
/// with no lock involved at all.
pub struct Pair {
    pub a: i32,
    pub b: i32,
}

// ---------------------------------------------------------------------
// if/else joins
// ---------------------------------------------------------------------

/// `[SUPPORTED]` Both branches of an `if`/`else` independently acquire and
/// release their own local write guard before the join; the guard never
/// survives past the branch that created it.
#[verify::stateful_lifetimes]
pub fn if_both_branches_acquire_write_release(lock: &Lock<i32>, b: bool) -> i32 {
    if b {
        let mut guard = lock.write();
        *guard.get_mut() += 1;
        let v = *guard.get();
        guard.release();
        v
    } else {
        let mut guard = lock.write();
        *guard.get_mut() += 2;
        let v = *guard.get();
        guard.release();
        v
    }
}

/// `[SUPPORTED]` Same shape as `if_both_branches_acquire_write_release`,
/// but with read guards on both branches, combined with an unrelated
/// value after the join.
#[verify::stateful_lifetimes]
pub fn if_both_branches_acquire_read_release(lock: &Lock<i32>, b: bool, extra: i32) -> i32 {
    let base = if b {
        let guard = lock.read();
        let v = *guard.get();
        guard.release();
        v
    } else {
        let guard = lock.read();
        let v = *guard.get();
        guard.release();
        v
    };
    base + extra
}

/// `[SUPPORTED]` Only the `true` branch ever touches the lock; the `false`
/// branch is entirely lock-free. The guard is local to the `true` branch
/// and never crosses the join, so there is nothing to reconcile.
#[verify::stateful_lifetimes]
pub fn if_only_one_branch_acquires(lock: &Lock<i32>, b: bool, fallback: i32) -> i32 {
    if b {
        let guard = lock.read();
        let v = *guard.get();
        guard.release();
        v
    } else {
        fallback
    }
}

/// `[SUPPORTED]` Asymmetric variant of `if_only_one_branch_acquires`: the
/// acquiring branch additionally *mutates* through the guard before
/// releasing, while the other branch performs unrelated arithmetic.
#[verify::stateful_lifetimes]
pub fn if_only_one_branch_acquires_asymmetric_use(lock: &Lock<i32>, b: bool, fallback: i32) -> i32 {
    if b {
        let mut guard = lock.write();
        *guard.get_mut() += 10;
        let v = *guard.get();
        guard.release();
        v
    } else {
        fallback * 2 + 1
    }
}

/// `[SUPPORTED]` A 3-way `if`/`else if`/`else` chain (desugars to nested
/// `if`/`else`, but exercises the multi-level join at the surface-syntax
/// level rather than via `match`): every one of the three branches
/// acquires and releases its own local guard before the join, mirroring
/// `match_three_arms_independent_guards` below for the `if`-chain surface
/// form instead of `match`.
#[verify::stateful_lifetimes]
pub fn else_if_chain_independent_guards(lock: &Lock<i32>, selector: i32) -> i32 {
    if selector == 0 {
        let guard = lock.read();
        let v = *guard.get();
        guard.release();
        v
    } else if selector == 1 {
        let mut guard = lock.write();
        *guard.get_mut() += 1;
        let v = *guard.get();
        guard.release();
        v
    } else {
        let guard = lock.read();
        let v = *guard.get();
        guard.release();
        v * 2
    }
}

// ---------------------------------------------------------------------
// Guard returned open across a join / function boundary
// ---------------------------------------------------------------------

/// `[SUPPORTED]` Both branches of an `if`/`else` return an **open**
/// (unreleased) guard directly as the function's result — the release
/// obligation is handed to the caller rather than discharged locally,
/// exactly like an ordinary `&mut` returned from `choose` below. The
/// branches are asymmetric: the `true` branch acquires and returns
/// immediately, while the `false` branch first performs unrelated
/// arithmetic before acquiring and returning. EXPECTED: since both
/// branches agree on the join shape ("an open write guard, to be released
/// by the caller"), this should be handled the same way `choose` is
/// handled today, just with a release-shaped backward function attached
/// to the returned guard instead of a plain value.
#[verify::stateful_lifetimes]
pub fn if_asymmetric_branches_return_open_guard(
    lock: &Lock<i32>,
    b: bool,
    bias: i32,
) -> WriteGuard<'_, i32> {
    if b {
        lock.write()
    } else {
        let _unused = bias * 2 + 1;
        lock.write()
    }
}

/// Enum used only by `match_join_returns_guard_enum` below, to unify a
/// `ReadGuard` and a `WriteGuard` (otherwise-incompatible types) into a
/// single type that can flow out of every arm of a `match`.
pub enum GuardKind<'a, T> {
    Read(ReadGuard<'a, T>),
    Write(WriteGuard<'a, T>),
}

/// `[SUPPORTED]` A 3-arm `match` where each arm acquires a *different
/// kind* of guard (`Read` in two arms, `Write` in the third) and wraps it
/// in the `GuardKind` enum so every arm produces the same Rust type at the
/// join. Every arm returns its guard open (unreleased) inside the enum,
/// handing the release obligation to the caller. EXPECTED: this is the
/// enum-carried analogue of `if_asymmetric_branches_return_open_guard`
/// above — the join shape is uniform ("an open guard of some kind, wrapped
/// in `GuardKind`"), but discharging the eventual release will require
/// matching on the enum variant to know which of `ReadGuard`'s or
/// `WriteGuard`'s backward function to invoke.
#[verify::stateful_lifetimes]
pub fn match_join_returns_guard_enum(lock: &Lock<i32>, selector: i32) -> GuardKind<'_, i32> {
    match selector {
        0 => GuardKind::Read(lock.read()),
        1 => GuardKind::Write(lock.write()),
        _ => GuardKind::Read(lock.read()),
    }
}

// ---------------------------------------------------------------------
// Early return
// ---------------------------------------------------------------------

/// `[SUPPORTED]` The guard is fully released before the (conditional)
/// early return, so nothing is left open at the point the function exits
/// on either path.
#[verify::stateful_lifetimes]
pub fn early_return_after_release(lock: &Lock<i32>, b: bool) -> i32 {
    let guard = lock.read();
    let v = *guard.get();
    guard.release();
    if b {
        return v;
    }
    v + 1
}

/// `[DIAGNOSTIC CANDIDATE]` A realistic bug shape: the early-return path
/// skips `release()` entirely, so the guard is leaked on that path while
/// the fallthrough path releases normally. Two exits of the same function
/// disagree on whether the guard is still open. EXPECTED: once release
/// obligations are tracked, this should eventually be flagged (or the
/// early-return path fixed to release first).
#[verify::stateful_lifetimes]
pub fn early_return_without_release(lock: &Lock<i32>, b: bool) -> i32 {
    let guard = lock.write();
    if b {
        // Guard never released on this path.
        return -1;
    }
    let v = *guard.get();
    guard.release();
    v
}

// ---------------------------------------------------------------------
// match with 3 arms / guard before match / guard inside arm
// ---------------------------------------------------------------------

/// `[SUPPORTED]` Match with 3 arms (satisfies both "match with 3 arms" and
/// "guard inside arm"): each arm acquires and releases its own local
/// guard, entirely independent of the other arms.
#[verify::stateful_lifetimes]
pub fn match_three_arms_independent_guards(lock: &Lock<i32>, selector: i32) -> i32 {
    match selector {
        0 => {
            let guard = lock.read();
            let v = *guard.get();
            guard.release();
            v
        }
        1 => {
            let mut guard = lock.write();
            *guard.get_mut() += 1;
            let v = *guard.get();
            guard.release();
            v
        }
        _ => {
            let guard = lock.read();
            let v = *guard.get();
            guard.release();
            v * 2
        }
    }
}

/// `[SUPPORTED]` "Guard before match": the guard is acquired *before* the
/// match on an unrelated selector; every one of the 3 arms ends the *same*
/// guard (with different work performed first), so all paths agree on the
/// guard being closed by the time control reaches the join after the
/// match.
#[verify::stateful_lifetimes]
pub fn guard_before_match_released_in_each_arm(lock: &Lock<i32>, selector: i32) -> i32 {
    let mut guard = lock.write();
    let result = match selector {
        0 => *guard.get(),
        1 => {
            *guard.get_mut() += 1;
            *guard.get()
        }
        _ => {
            *guard.get_mut() += 2;
            *guard.get() * 2
        }
    };
    guard.release();
    result
}

/// `[DIAGNOSTIC CANDIDATE]` Same "guard before match" shape as
/// `guard_before_match_released_in_each_arm`, but one arm forgets to
/// release before falling through to the caller. Since the guard was
/// created before the match, this leak is easy to introduce by accident
/// (unlike a guard created fresh inside a single arm). EXPECTED: this
/// should eventually be caught once release obligations are tracked
/// through match joins.
#[verify::stateful_lifetimes]
pub fn guard_before_match_one_arm_forgets_release(lock: &Lock<i32>, selector: i32) -> i32 {
    let mut guard = lock.write();
    match selector {
        0 => {
            let v = *guard.get();
            guard.release();
            v
        }
        1 => {
            *guard.get_mut() += 1;
            let v = *guard.get();
            guard.release();
            v
        }
        _ => {
            // Forgotten `guard.release()` on this arm.
            *guard.get_mut() += 2;
            *guard.get()
        }
    }
}

/// `[SUPPORTED]` Nested `match`: an outer match on `outer_sel` contains an
/// inner match on `inner_sel`. A single guard, acquired at the top, is
/// released consistently along every one of the 4 leaf combinations,
/// exercising a two-level join instead of a single flat one.
#[verify::stateful_lifetimes]
pub fn nested_match_guard_threading(lock: &Lock<i32>, outer_sel: bool, inner_sel: bool) -> i32 {
    let mut guard = lock.write();
    let result = match outer_sel {
        true => match inner_sel {
            true => {
                *guard.get_mut() += 1;
                *guard.get()
            }
            false => *guard.get(),
        },
        false => match inner_sel {
            true => *guard.get(),
            false => {
                *guard.get_mut() -= 1;
                *guard.get()
            }
        },
    };
    guard.release();
    result
}

/// `[SUPPORTED]` `match` with guard clauses (`pattern if condition`): the
/// pattern match on `selector` alone is refined by an extra boolean guard
/// condition on each of the two non-wildcard arms. Since match guards are
/// just ordinary boolean tests inserted between pattern matching and arm
/// selection, and every arm (guarded or not) acquires and releases its own
/// local guard, this should compose with match-join handling exactly like
/// `match_three_arms_independent_guards` above.
#[verify::stateful_lifetimes]
pub fn match_with_guard_clauses(lock: &Lock<i32>, selector: i32, threshold: i32) -> i32 {
    match selector {
        n if n > threshold => {
            let guard = lock.read();
            let v = *guard.get();
            guard.release();
            v
        }
        n if n < -threshold => {
            let mut guard = lock.write();
            *guard.get_mut() -= 1;
            let v = *guard.get();
            guard.release();
            v
        }
        _ => {
            let guard = lock.read();
            let v = *guard.get();
            guard.release();
            -v
        }
    }
}

// ---------------------------------------------------------------------
// Short-circuit boolean operators
// ---------------------------------------------------------------------

/// `[SUPPORTED]` `&&` short-circuits: the guard is only acquired (and
/// released) when `b` is `true`, since the right-hand side of `&&` is not
/// evaluated at all when the left-hand side is `false`.
#[verify::stateful_lifetimes]
pub fn short_circuit_and_guard_condition(lock: &Lock<i32>, b: bool) -> bool {
    b && {
        let guard = lock.read();
        let v = *guard.get();
        guard.release();
        v > 0
    }
}

/// `[SUPPORTED]` `||` short-circuits: the guard is only acquired (and
/// released) when `b` is `false`, mirroring
/// `short_circuit_and_guard_condition` for the other short-circuit
/// operator.
#[verify::stateful_lifetimes]
pub fn short_circuit_or_guard_fallback(lock: &Lock<i32>, b: bool) -> bool {
    b || {
        let guard = lock.read();
        let v = *guard.get();
        guard.release();
        v > 0
    }
}

// ---------------------------------------------------------------------
// if let / while let
// ---------------------------------------------------------------------

/// `[SUPPORTED]` `if let` with no `else`: the join is between "acquired,
/// used, and released" (the `Some` path) and "nothing happened at all"
/// (the implicit empty `else`), which never touches the lock.
#[verify::stateful_lifetimes]
pub fn if_let_try_write_no_else(lock: &Lock<i32>) {
    if let Some(mut guard) = lock.try_write() {
        *guard.get_mut() += 1;
        guard.release();
    }
}

/// `[SUPPORTED]` `if let`/`else`: the `Some` branch acquires and releases a
/// read guard; the `else` branch is an unrelated fallback computation that
/// never touches the lock.
#[verify::stateful_lifetimes]
pub fn if_let_else_try_read_with_fallback(lock: &Lock<i32>, fallback: i32) -> i32 {
    if let Some(guard) = lock.try_read() {
        let v = *guard.get();
        guard.release();
        v
    } else {
        fallback
    }
}

/// `[SUPPORTED]` `let ... else`: the `Some` arm binds the guard and falls
/// through to release it; the `else` arm diverges (`return`) before ever
/// touching the lock, so the only path that reaches the release is the one
/// where the guard was actually acquired. This is the `let`-`else` form of
/// the same "if let with no else" shape as `if_let_try_write_no_else`
/// above, exercising the join between "continue with an open guard" and
/// "diverge" rather than between "continue with an open guard" and
/// "continue without one".
#[verify::stateful_lifetimes]
pub fn let_else_try_read_or_return(lock: &Lock<i32>, fallback: i32) -> i32 {
    let Some(guard) = lock.try_read() else {
        return fallback;
    };
    let v = *guard.get();
    guard.release();
    v
}

// Baseline note: both former `while let` shapes currently fail in
// `InterpBorrows.destructure_abs` (`InterpBorrows.ml:2076`). Their focused
// reproducers live in `lt-stateful-control-known-failures.rs`.

// ---------------------------------------------------------------------
// Guard held around a callback
// ---------------------------------------------------------------------

/// `[SUPPORTED]` A read guard is held across the invocation of a generic
/// callback `f`, which only observes the guarded value through `&T` and
/// cannot itself extend the guard's lifetime (its signature ties the
/// reference to the call). This is the simplest "guard around a callback"
/// shape and is expected to remain supported: the callback call site is
/// just an ordinary opaque/generic call sandwiched between acquire and
/// release, with no branching of its own.
#[verify::stateful_lifetimes]
pub fn guard_around_callback_read<T, F: FnOnce(&T) -> i32>(lock: &Lock<T>, f: F) -> i32 {
    let guard = lock.read();
    let result = f(guard.get());
    guard.release();
    result
}

/// `[SUPPORTED]` Same shape as `guard_around_callback_read`, but the
/// callback itself contains its own internal branching (an `if`/`else`).
/// The guard is not touched by the callback's branches at all, so this
/// should compose with the "if both branches" join handling inside `f`
/// independently of the guard's own acquire/release pair around the call.
#[verify::stateful_lifetimes]
pub fn guard_around_callback_with_internal_branch<T, F: Fn(&T, bool) -> i32>(
    lock: &Lock<T>,
    f: F,
    branch: bool,
) -> i32 {
    let guard = lock.read();
    let result = if branch {
        f(guard.get(), true)
    } else {
        f(guard.get(), false)
    };
    guard.release();
    result
}

/// `[DIAGNOSTIC CANDIDATE]` A guard is held across an explicit panic branch.
/// If the branch panics, control leaves the function via
/// `fail` without ever reaching `guard.release()`. EXPECTED: this is one of
/// the most realistic real-world bug shapes ("panicking while holding a
/// lock"); once guards have real release obligations, panicking paths
/// through code that holds an open guard should be flagged, since Aeneas's
/// `fail` short-circuits the pure computation without running any
/// destructor-like cleanup.
#[verify::stateful_lifetimes]
pub fn guard_around_panicking_callback(lock: &Lock<i32>, panic_now: bool, x: i32) -> i32 {
    let guard = lock.write();
    let v = *guard.get();
    let result = if panic_now {
        panic!("panic while guard is open")
    } else {
        v + x
    };
    guard.release();
    result
}

#[verify::opaque]
pub fn maybe_fail(x: i32) -> Result<i32, u32> {
    unimplemented!()
}

/// `[DIAGNOSTIC CANDIDATE]` The guard is open across a branch whose taken
/// arm may return an ordinary Rust `Err` through `?`. That early exit is
/// `ok (Err e)`, not monadic `fail`, but it still skips `release`.
#[verify::stateful_lifetimes]
pub fn guard_branch_with_try(lock: &Lock<i32>, take_fallible: bool, x: i32) -> Result<i32, u32> {
    let guard = lock.write();
    let result = if take_fallible { maybe_fail(x)? } else { x };
    guard.release();
    Ok(result)
}

// ---------------------------------------------------------------------
// No-regression fixtures: ordinary control-flow joins, no lock involved
// ---------------------------------------------------------------------

/// `[NO-REGRESSION]` The classic `choose` pattern (see `paper.rs` and
/// `lt-stateful-reborrows.rs`), with no lock involved at all: an `if`/else
/// join over two ordinary `&mut i32` borrows. EXPECTED: today's plain
/// backward-function translation `T -> (T, T)`, entirely unaffected by
/// stateful lifetimes.
pub fn choose<'a, T>(b: bool, x: &'a mut T, y: &'a mut T) -> &'a mut T {
    if b {
        x
    } else {
        y
    }
}

/// `[NO-REGRESSION]` A `match` with 3 arms projecting into different
/// fields of two ordinary `&mut Pair` borrows, with no lock in sight.
/// EXPECTED: today's plain field-projection backward-function chain,
/// unaffected by this feature. No `#[verify::stateful_lifetimes]` attribute
/// here: this fixture involves no `Lock`/`Guard` at all, so tagging it
/// would misleadingly suggest the feature has something to track here —
/// compare with `choose` above, which is likewise `[NO-REGRESSION]` and
/// likewise untagged.
pub fn match_field_projection_no_lock<'a>(
    selector: i32,
    x: &'a mut Pair,
    y: &'a mut Pair,
) -> &'a mut i32 {
    match selector {
        0 => &mut x.a,
        1 => &mut x.b,
        _ => &mut y.a,
    }
}
