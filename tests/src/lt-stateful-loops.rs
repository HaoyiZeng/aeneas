//@ [!lean] skip
//@ [lean] aeneas-args=-loops-to-rec
//! EXPECTED AFTER IMPLEMENTATION:
//! This file complements `lt-stateful-control.rs`, `lt-stateful-signatures.rs`,
//! and `lt-stateful-reborrows.rs`, focusing on how an *effectful guard*
//! (acquired from a `Lock` and ended via `release`, standing in for a
//! future `Drop`-driven release) behaves across **loops**: `break`,
//! `continue`, early `return`, nested loops, a guard carried across
//! iterations (rather than re-acquired each time), swapping which guard is
//! held mid-loop, ordered acquisition of two guards, the different Rust
//! loop forms (`for`, `while`, iterator combinators), a guard held across a
//! recursive call, and a guard escaping the loop as its own result.
//!
//! Once `#[verify::stateful_lifetimes]` is implemented, a loop's fixed
//! point/invariant computation is expected to treat an open stateful guard
//! exactly like any other loop-carried mutable value: if the same guard
//! value flows unchanged from the loop header, through every iteration's
//! back edge, to the loop's exit, the invariant is just "the guard is open
//! with such-and-such contents" — analogous to how a loop-carried `&mut`
//! accumulator is handled today (see `sum_with_mut_borrows` in
//! `loops-rec.rs`). Problems arise when the guard's *shape* differs
//! between iterations or between exits of the same loop (see the baseline
//! notes near the end of this file) — this is the loop
//! analogue of the join-shape-mismatch problem documented in
//! `lt-stateful-control.rs`, and is exactly the kind of mismatch
//! `-strict-joins` reports as an error for ordinary borrows today rather
//! than duplicating code (see `-strict-joins` in `src/Main.ml`).
//!
//! **Blanket caveat — failure and unwinding:** every `[SUPPORTED]` tag
//! below implicitly assumes the *normal* (non-failing, non-diverging)
//! iteration/exit paths only. Aeneas's pure translation models a Rust
//! panic (and, more generally, any path that would unwind the stack in a
//! real execution) as `fail`, which short-circuits the surrounding
//! `Result` computation immediately — skipping every statement lexically
//! between the failure point and the function's exit, in particular any
//! `release()` call that would otherwise have run on that iteration.
//! Concretely: if a loop body below can panic (e.g. an arithmetic
//! overflow, an indexing failure, or a recursive/closure call that itself
//! panics) while a guard is open for that iteration, the pure semantics
//! leaks that guard on the failing path exactly like the early-`return`
//! leak in `return_from_loop_without_release` does, regardless of how the
//! function is tagged. This caveat is non-vacuous today: several supported
//! loop bodies perform overflow-checked arithmetic while a guard is open.
//!
//! Each function below is tagged in its doc comment with one of:
//!   - `[SUPPORTED]`: the guard's open/closed shape is uniform across every
//!     iteration and every exit of the loop; expected to remain accepted,
//!     with real per-iteration release-bookkeeping attached once the
//!     feature lands.
//!   - `[DIAGNOSTIC CANDIDATE]`: at least one iteration or exit leaks the
//!     guard, or the guard's shape genuinely differs between iterations or
//!     exits; expected to eventually be rejected or specifically handled
//!     once release-obligations are tracked through loops.
//!   - `[NO-REGRESSION]`: no lock/guard is involved; included to confirm
//!     ordinary loop-carried `&mut` translation must remain byte-for-byte
//!     unaffected by this feature.
//!   - `[SUPPORTED, tentative]`: reserved for sum-shaped loop invariants;
//!     the current reproducer lives in
//!     `lt-stateful-loop-replace-known-failures.rs`.
//!
//! We use `-loops-to-rec` (translating loops to recursive Lean functions)
//! since that is the loop-translation mode with the most mature proof
//! infrastructure (see the `aeneas-lean-core` skill file, "Loop
//! Translation: Prefer `-loops-to-rec`"), making these fixtures directly
//! reusable once proof work on stateful lifetimes begins.
//!
//! CURRENT BASELINE:
//! `#[verify::stateful_lifetimes]` is an inert tool attribute today
//! (registered via `#![register_tool(verify)]` but not yet interpreted by
//! Aeneas). `Lock`, `ReadGuard`, and `WriteGuard` are `#[verify::opaque]`,
//! so every method call on them is extracted today as an ordinary opaque
//! call with no linear/release tracking whatsoever, and loops are
//! extracted using the existing (non-stateful) loop-translation machinery.
//! Every function in this file — including the ones tagged `[DIAGNOSTIC
//! CANDIDATE]` — is expected to compile and
//! extract fine today: nothing currently forces a guard to be released on
//! every iteration or every exit, and nothing currently requires a single
//! shared "guard shape" invariant across loop iterations, since guards are
//! just opaque values with no special loop-invariant treatment. This file
//! exists so that, once the feature lands, these shapes can be used
//! (unmodified, or with minimal changes) as regression and
//! diagnostic-acceptance fixtures.
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
    /// backward function `T -> Result Guard` per guard value, threaded
    /// once per loop iteration when the guard is loop-carried.
    #[verify::opaque]
    pub fn get_mut(&mut self) -> &mut T {
        unimplemented!()
    }

    /// Explicit release. EXPECTED: `Guard -> Result Unit` backward function.
    #[verify::opaque]
    pub fn release(self) {}
}

// ---------------------------------------------------------------------
// Acquire/release each iteration (while / for), break, continue
// ---------------------------------------------------------------------

// Baseline note: mutating a freshly acquired guard via `get_mut` and
// releasing it within the same loop iteration fails in
// `InterpBorrows.destructure_abs`. See
// `lt-stateful-control-known-failures.rs`.

/// `[SUPPORTED]` Read-guard analogue of
/// `acquire_release_each_iteration_while`, using a `for` loop. The mutable
/// `get_mut` variant remains a known failure.
#[verify::stateful_lifetimes]
pub fn acquire_release_each_iteration_for(lock: &Lock<i32>, n: u32) -> i32 {
    let mut total = 0;
    for _ in 0..n {
        let guard = lock.read();
        total += *guard.get();
        guard.release();
    }
    total
}

/// `[SUPPORTED]` `break`: the guard is always released before the `break`
/// that ends the loop, so the loop's exit state never has an open guard.
#[verify::stateful_lifetimes]
pub fn loop_with_break_after_release(lock: &Lock<i32>, n: u32, stop_value: i32) -> u32 {
    let mut i = 0;
    loop {
        if i >= n {
            break;
        }
        let guard = lock.read();
        let v = *guard.get();
        guard.release();
        if v == stop_value {
            break;
        }
        i += 1;
    }
    i
}

/// `[SUPPORTED]` The guard is only acquired on some iterations (a
/// conditional acquire), and is always released before any possible
/// `break`, so the "guard open?" shape at the `break` point is uniformly
/// "closed" regardless of which iteration triggers it.
#[verify::stateful_lifetimes]
pub fn while_loop_conditional_acquire_then_break(lock: &Lock<i32>, n: u32, stop_at: i32) -> bool {
    let mut i = 0;
    while i < n {
        if i % 2 == 0 {
            let guard = lock.write();
            let v = *guard.get();
            guard.release();
            if v == stop_at {
                break;
            }
        }
        i += 1;
    }
    i < n
}

/// `[SUPPORTED]` `continue`: the guard is acquired and released before the
/// `continue` on every qualifying iteration, so the guard is always closed
/// at the back edge.
#[verify::stateful_lifetimes]
pub fn loop_with_continue_after_release(lock: &Lock<i32>, n: u32) -> i32 {
    let mut i = 0;
    let mut total = 0;
    while i < n {
        let guard = lock.read();
        let v = *guard.get();
        guard.release();
        i += 1;
        if v < 0 {
            continue;
        }
        total += v;
    }
    total
}

/// `[SUPPORTED]` The guard is only acquired on iterations that do *not*
/// hit the `continue` (the `continue` fires *before* the lock is ever
/// touched this round), so at the back edge the guard is uniformly
/// "never opened this round".
#[verify::stateful_lifetimes]
pub fn loop_with_continue_skip_acquire(lock: &Lock<i32>, n: u32) -> i32 {
    let mut i = 0;
    let mut total = 0;
    while i < n {
        i += 1;
        if i % 2 == 0 {
            continue;
        }
        let guard = lock.write();
        total += *guard.get();
        guard.release();
    }
    total
}

/// `[SUPPORTED]` A `for` loop over a *slice of locks* (rather than a
/// single, fixed `lock`): each iteration acquires a guard on a *different*
/// `Lock<i32>` identity (`locks[i]`), uses it, and releases it before
/// moving to the next index. The loop invariant only needs to describe
/// the *shape* "some lock's guard is open, then closed, each iteration" —
/// never the identity of a fixed lock — contrasting with
/// `guard_conditionally_replaced_in_loop` in
/// `lt-stateful-loop-replace-known-failures.rs`, where the invariant must
/// track which of exactly two named locks is currently held.
#[verify::stateful_lifetimes]
pub fn for_loop_varying_lock_identity(locks: &[Lock<i32>]) -> i32 {
    let mut total = 0;
    for lock in locks {
        let guard = lock.read();
        total += *guard.get();
        guard.release();
    }
    total
}

// Baseline note: labelled break/continue from an inner loop to an outer
// loop is rejected in `PrePasses`; see
// `lt-stateful-labelled-break-known-failures.rs`.

// ---------------------------------------------------------------------
// Return from a loop
// ---------------------------------------------------------------------

/// `[SUPPORTED]` The guard is released before the early `return` from
/// inside the loop, so the function's exit state (whether via the early
/// `return` or the loop completing normally) is uniformly "guard closed".
#[verify::stateful_lifetimes]
pub fn return_from_loop_after_release(lock: &Lock<i32>, n: u32, bail_at: i32) -> i32 {
    let mut i = 0;
    while i < n {
        let guard = lock.write();
        let v = *guard.get();
        guard.release();
        if v == bail_at {
            return v;
        }
        i += 1;
    }
    0
}

/// `[DIAGNOSTIC CANDIDATE]` The early `return` from inside the loop skips
/// `release()` entirely, leaking the guard on that exit path, while the
/// loop completing normally never had this problem (the guard is
/// re-acquired and released every iteration). EXPECTED: once release
/// obligations are tracked, the early-return exit and the normal-exit
/// path must agree on the guard's shape; this mismatch should eventually
/// be flagged.
#[verify::stateful_lifetimes]
pub fn return_from_loop_without_release(lock: &Lock<i32>, n: u32, bail_at: i32) -> i32 {
    let mut i = 0;
    while i < n {
        let guard = lock.write();
        if *guard.get() == bail_at {
            // Guard never released on this path.
            return -1;
        }
        guard.release();
        i += 1;
    }
    0
}

/// `[SUPPORTED]` Three structurally distinct exits, all agreeing on the
/// guard's shape ("closed"): (1) an early `return` from inside the loop
/// once the guard reveals a sentinel value, (2) a `break` once the
/// counter reaches its halfway point, and (3) falling out of the `while`
/// normally (either because the loop condition is false from the start,
/// or after the `break` above). Every one of the three paths releases (or
/// never opens) the guard before the corresponding exit is taken, so —
/// unlike `unsupported_loop_divergent_exit_guard_state` in
/// `lt-stateful-control-known-failures.rs`, which has two exits with
/// genuinely different guard shapes — all three exits here agree.
#[verify::stateful_lifetimes]
pub fn loop_with_three_way_exit_consistent_release(lock: &Lock<i32>, n: u32, sentinel: i32) -> i32 {
    let mut i = 0;
    while i < n {
        let guard = lock.read();
        let v = *guard.get();
        guard.release();
        if v == sentinel {
            // Exit 1: early return, guard already released.
            return v;
        }
        i += 1;
        if i == n / 2 {
            // Exit 2: break, guard already released (nothing open here).
            break;
        }
    }
    // Exit 3: normal fallthrough (loop condition false from the start, or
    // reached via the break above); the guard was never left open on any
    // path that reaches this point.
    0
}

// ---------------------------------------------------------------------
// Nested loops
// ---------------------------------------------------------------------

/// `[SUPPORTED]` Nested loops where each loop level manages its own,
/// entirely independent guard: the outer loop's guard is unrelated to the
/// inner loop's guard, and both are fully acquired/released within their
/// own iteration.
#[verify::stateful_lifetimes]
pub fn nested_loops_independent_guards(lock: &Lock<i32>, outer_n: u32, inner_n: u32) -> i32 {
    let mut total = 0;
    for _ in 0..outer_n {
        let outer_guard = lock.read();
        let outer_v = *outer_guard.get();
        outer_guard.release();
        for _ in 0..inner_n {
            let inner_guard = lock.read();
            total += *inner_guard.get() + outer_v;
            inner_guard.release();
        }
    }
    total
}

/// `[SUPPORTED]` A single write guard is carried through two nested loops
/// and released after both complete.
#[verify::stateful_lifetimes]
pub fn nested_loops_shared_outer_guard(lock: &Lock<i32>, outer_n: u32, inner_n: u32) {
    let mut guard = lock.write();
    for _ in 0..outer_n {
        for _ in 0..inner_n {
            *guard.get_mut() += 1;
        }
    }
    guard.release();
}

// ---------------------------------------------------------------------
// Loop-carried guard acquired before the loop
// ---------------------------------------------------------------------

/// `[SUPPORTED]` The direct loop-carried write-guard shape: acquire once,
/// mutate on every back edge, release once after the loop.
#[verify::stateful_lifetimes]
pub fn loop_carried_guard_acquired_before_loop(lock: &Lock<i32>, n: u32) -> i32 {
    let mut guard = lock.write();
    let mut i = 0;
    while i < n {
        *guard.get_mut() += 1;
        i += 1;
    }
    let result = *guard.get();
    guard.release();
    result
}

// ---------------------------------------------------------------------
// Guard conditionally replaced / two guards ordered
// ---------------------------------------------------------------------

// Baseline notes: conditional guard replacement fails in
// `InterpMatchCtxs` (`lt-stateful-loop-replace-known-failures.rs`).
// ADT-carried and ordered-two-guard mutation loops fail in
// `InterpBorrows.destructure_abs`
// (`lt-stateful-control-known-failures.rs`).

// ---------------------------------------------------------------------
// Iterator combinators
// ---------------------------------------------------------------------

// Backend note: the iterator-combinator form translates through Aeneas but
// its generated Lean does not elaborate. See
// `lt-stateful-loop-backend-failures.rs`.

// ---------------------------------------------------------------------
// Recursive function holding a guard
// ---------------------------------------------------------------------

/// `[SUPPORTED]` A recursive function acquires a write guard and keeps it
/// open *across* the recursive call (rather than releasing before
/// recursing), releasing only after the recursive call returns. This
/// models a guard held across a whole chain of stack frames rather than
/// within a single loop iteration; EXPECTED to require the same
/// backward-release-threading treatment as an ordinary `&mut` held across
/// a recursive call.
///
/// **Abstraction caveat (deadlock):** `Lock` is a purely opaque,
/// uninterpreted type here — `#[verify::opaque]` gives it no runtime
/// semantics at all, so nothing in this model prevents re-entering
/// `lock.write()` on the very same `lock` value while an outer frame's
/// guard is still open, and every recursive call below does exactly that.
/// A genuine non-reentrant `Mutex`/`RwLock` implementing this same source
/// text would deadlock (or panic, for a "detect self-deadlock" flavor of
/// lock) the moment `depth >= 2`, since the inner call's `lock.write()`
/// would block forever on a lock its own call stack already holds. This
/// fixture is included purely as a *type-level* release-threading
/// exercise — it deliberately does not model real mutual-exclusion
/// semantics — and should not be read as evidence that recursive
/// re-locking of the same lock identity is a safe or realistic pattern.
/// Contrast with `recurse_moving_same_guard` below, which threads a
/// single already-open guard *through* the recursion (never re-acquiring
/// the lock at any depth) and so has no such deadlock reading.
#[verify::stateful_lifetimes]
pub fn recurse_holding_guard_across_call(lock: &Lock<i32>, depth: u32) {
    if depth == 0 {
        return;
    }
    let mut guard = lock.write();
    *guard.get_mut() += 1;
    recurse_holding_guard_across_call(lock, depth - 1);
    guard.release();
}

/// `[SUPPORTED]` Unlike `recurse_holding_guard_across_call` above (which
/// acquires its own local guard every frame and holds it open *around*
/// the recursive call, re-locking the same `Lock` at every depth), this
/// function receives an already-open guard as a parameter and *moves* that
/// very same guard value into the recursive call, one level deeper each
/// time, until the base case hands it back out. The guard's identity is
/// threaded through the whole call chain rather than each frame managing
/// its own — and since the lock is only ever acquired once (by the
/// caller, before any recursion starts), this shape has no re-locking
/// deadlock reading at all.
#[verify::stateful_lifetimes]
pub fn recurse_moving_same_guard_forward<'a>(
    mut guard: WriteGuard<'a, i32>,
    depth: u32,
) -> WriteGuard<'a, i32> {
    if depth == 0 {
        return guard;
    }
    *guard.get_mut() += 1;
    recurse_moving_same_guard_forward(guard, depth - 1)
}

/// `[SUPPORTED]` Wrapper that acquires a guard, threads it through
/// `recurse_moving_same_guard_forward` (moving the same guard value
/// through every recursive call rather than re-acquiring the lock at each
/// depth), and releases it once the guard comes back out at the top.
#[verify::stateful_lifetimes]
pub fn recurse_moving_same_guard(lock: &Lock<i32>, depth: u32) -> i32 {
    let guard = lock.write();
    let guard = recurse_moving_same_guard_forward(guard, depth);
    let v = *guard.get();
    guard.release();
    v
}

// ---------------------------------------------------------------------
// Guard scope strictly inside the loop body / loop returning the guard
// ---------------------------------------------------------------------

// Baseline notes: a nested body-local guard fails in
// `InterpBorrows.destructure_abs`; guard-valued loop exits fail in
// `InterpJoin`; labelled guard exits from nested loops fail in `PrePasses`.
// See `lt-stateful-control-known-failures.rs`,
// `lt-stateful-loop-return-known-failures.rs`, and
// `lt-stateful-labelled-return-known-failures.rs`.

// ---------------------------------------------------------------------
// Known-unsupported loop/join/closure-escape baseline notes
// ---------------------------------------------------------------------

// A guard moved into a stored `Box<dyn FnOnce()>` transfers its obligation
// to the eventual caller. The current baseline rejects the dynamic trait
// earlier in `SymbolicToPureTypes.ml:547`; see
// `lt-stateful-dyn-loop-known-failures.rs`.
//
// An optional per-iteration guard needs an Option-shaped loop invariant,
// while two exits that disagree on open/closed guard state have no uniform
// invariant at all. Both currently fail earlier in
// `InterpBorrows.destructure_abs`; see
// `lt-stateful-control-known-failures.rs`.

// ---------------------------------------------------------------------
// No-regression fixture: ordinary loop-carried &mut, no lock involved
// ---------------------------------------------------------------------

/// `[NO-REGRESSION]` A plain loop-carried `&mut i32` accumulator over a
/// slice, with no lock/guard anywhere. EXPECTED: today's ordinary
/// loop-translation machinery (as in `sum_with_mut_borrows` in
/// `loops-rec.rs`), entirely unaffected by stateful lifetimes.
pub fn no_regression_plain_sum_loop(acc: &mut i32, xs: &[i32]) {
    for i in 0..xs.len() {
        *acc += xs[i];
    }
}
