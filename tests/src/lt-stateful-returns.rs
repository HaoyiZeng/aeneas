//@ [!lean] skip
//! # Stateful lock/guard lifetime fixtures — RETURN-PATH variants
//!
//! This file stress-tests how the Lean backend threads an *opaque* stateful
//! "guard" value (conceptually: a RAII lock guard) across the many shapes a
//! return path can take: returned directly to the caller, moved into a
//! callee, consumed by a dedicated helper, produced via an early `return`,
//! produced from `if`/`match` branches, threaded through `Option`/`Result`
//! via `?` (including doubly-nested `Option`), returned from a nested
//! helper, wrapped inside `Option`/`Result`/tuples, replaced before return,
//! produced inside a closure (in the focused known-failure companion), and
//! returned from every kind of "normal"
//! (non-early-return) control-flow tail position (`if`, `match`, `loop`
//! `break`) — including a genuinely multi-iteration loop and a nested
//! `match` inside a loop. Labelled breaks across live nested loops remain
//! isolated known failures. It also exercises two
//! guard-release *disciplines* (who releases: the callee, before ever
//! returning the guard, vs. the caller, after receiving it) and a case
//! where every branch of a `match`/`if` performs its own explicit,
//! symmetric cleanup via `release`.
//!
//! `Lock` and `Guard<'_>` are marked `#[verify::opaque]`, so Aeneas has no
//! notion of their internal representation and — critically — no `Drop`
//! glue: unlike a real `MutexGuard`, nothing here is ever implicitly
//! released when a binding goes out of scope. This is intentional: it lets
//! us test how the pure backend threads an opaque, borrow-carrying value
//! through control flow without conflating that with modeling `Drop`
//! (which Aeneas does not attempt for opaque types anyway).
//!
//! `#[verify::stateful_lifetimes]` uses the lifetime-centric semantics
//! defined in `lt-stateful-signatures.rs`: bare form marks all lifetime
//! parameters of a function, while named form marks only those listed. It
//! is **tentative / exploratory** and is not interpreted by Aeneas today.
//! Because
//! `verify` is a registered tool (`#![register_tool(verify)]`), `rustc`
//! itself accepts the attribute syntactically without complaint — but that
//! is *not* the same as silence: Charon's own attribute parser
//! (`parse_special_attr` in `translate_meta.rs`) actively inspects every
//! `verify::*` attribute, and `stateful_lifetimes` is not one of the names
//! it special-cases (only `opaque`, `exclude`, `transparent`, `rename`,
//! `variants_prefix`, `variants_suffix`, `start_from`, and `test` are).
//! Falling through to the `_ => None` arm turns it into an `Unrecognized
//! attribute` error, which `register_error!` reports at `Level::WARNING` —
//! so today Charon emits one such (non-fatal, translation-continuing)
//! warning per annotated item in this file. It is included purely so these
//! fixtures keep compiling — and keep surfacing that warning — unchanged
//! if/when the attribute becomes meaningful.
//!
//! ## EXPECTED
//! Every function below should extract and translate to a pure Lean
//! definition in the `Result` monad. Since `acquire` / `release` /
//! `consume_guard` / `peek` are opaque, Aeneas should treat them as
//! uninterpreted (axiomatized) calls and simply thread the resulting
//! `Guard` value through the generated code. The shared-borrow-only
//! `Guard<'_>` region is erased today, so those scenarios deliberately
//! carry no backward function. The `MutGuard<'_>` scenarios below are the
//! corresponding obligation-carrying tests: their `&mut Lock` region
//! produces a real backward that must escape through the return path.
//!
//! ## CURRENT
//! As of this writing, the direct-return, branch, and helper-call patterns
//! are expected to translate without issue, mirroring the existing
//! opaque-borrow fixtures `opaque-mut-region.rs` and
//! `loop-shared-borrow-proj.rs`. The chained-`?` / doubly-nested-`Option`
//! scenarios near the end of the file are more speculative: they are
//! included to surface any gaps in the monadic threading of an opaque
//! value through those particular control-flow shapes. If one of them
//! turns out to expose a genuine limitation, prefer splitting it into its
//! own dedicated fixture (with an explicit `known-failure` marker) rather
//! than silently weakening this file.
//!
//! Note on the original `loop { break .. }` scenario: it used to read
//! `loop { break acquire(lock); }`, which always terminates on its very
//! first iteration. Such a loop has no real back-edge, so once translated
//! its recursive `_loop0` helper would hit its base case immediately and
//! never actually recurse — effectively "erasing" the loop into a
//! straight-line call and defeating the point of stressing the recursive-
//! loop machinery. That scenario has been replaced below by one that
//! genuinely iterates (see [`loop_break_with_guard`]).
//!
//! Note on the closure-returns-a-guard scenario: the original "Scenario 14"
//! (a closure capturing `lock` by shared reference and returning `acquire
//! (lock)` from its body, called once immediately) turned out to be exactly
//! such a genuine limitation — Aeneas errors out (`Can't end abstraction ...
//! as it is set as non-endable`) while translating the closure's
//! synthesized `call` operator. Per the guidance above, it has been split
//! into its own dedicated fixture,
//! `lt-stateful-return-closure-known-failures.rs`,
//! rather than silently weakening this file.

#![feature(register_tool)]
#![register_tool(verify)]

use std::marker::PhantomData;

// ---------------------------------------------------------------------------
// Opaque lock/guard vocabulary shared by every scenario below.
// ---------------------------------------------------------------------------

/// Opaque handle representing exclusive access to some resource. Aeneas
/// never looks inside it.
#[verify::opaque]
pub struct Lock {
    _priv: u32,
}

/// Opaque RAII-shaped guard borrowing from a `Lock`. In real code this
/// would release the lock on `Drop`; here it is opaque, so Aeneas treats
/// acquisition/release purely as black-box calls and never models `Drop`.
///
#[verify::opaque]
pub struct Guard<'a> {
    lock: &'a Lock,
}

/// Opaque acquire operation. Its elided lifetime is the region selected by
/// the tentative marker.
#[verify::stateful_lifetimes]
#[verify::opaque]
pub fn acquire(l: &Lock) -> Guard<'_> {
    unimplemented!()
}

/// Opaque release operation, consuming the guard by value.
#[verify::stateful_lifetimes]
#[verify::opaque]
pub fn release(g: Guard<'_>) {
    unimplemented!()
}

/// Opaque helper that consumes a guard by value and returns a scalar,
/// standing in for "do some work while holding the lock, then finish".
#[verify::stateful_lifetimes]
#[verify::opaque]
pub fn consume_guard(g: Guard<'_>) -> u32 {
    unimplemented!()
}

/// Opaque helper that only inspects a guard via a shared borrow.
#[verify::opaque]
pub fn peek(g: &Guard<'_>) -> u32 {
    unimplemented!()
}

/// Mutable-borrow guard used to make return-path backward obligations
/// observable in today's generated Lean.
#[verify::opaque]
pub struct MutGuard<'a> {
    _marker: PhantomData<&'a mut Lock>,
}

#[verify::stateful_lifetimes]
#[verify::opaque]
pub fn acquire_mut(lock: &mut Lock) -> MutGuard<'_> {
    unimplemented!()
}

#[verify::stateful_lifetimes]
#[verify::opaque]
pub fn release_mut(guard: MutGuard<'_>) {
    unimplemented!()
}

// ---------------------------------------------------------------------------
// Scenario 1: guard returned directly to the caller, no local `release`.
// ---------------------------------------------------------------------------

/// The guard escapes to the caller untouched; the caller becomes
/// responsible for eventually releasing it (or not — nothing enforces
/// that, since `Guard` is opaque and has no `Drop` glue).
#[verify::stateful_lifetimes]
pub fn return_guard_no_release(lock: &Lock) -> Guard<'_> {
    acquire(lock)
}

/// Mutable counterpart of `return_guard_no_release`. Baseline EXPECTED:
/// the returned guard carries a backward `MutGuard -> Lock` to the caller.
#[verify::stateful_lifetimes]
pub fn return_mut_guard_no_release(lock: &mut Lock) -> MutGuard<'_> {
    acquire_mut(lock)
}

/// The same mutable obligation wrapped in `Option`; the backward must
/// account for both `Some guard` and `None`.
#[verify::stateful_lifetimes]
pub fn return_mut_guard_in_option(lock: &mut Lock, enabled: bool) -> Option<MutGuard<'_>> {
    if enabled {
        Some(acquire_mut(lock))
    } else {
        None
    }
}

/// Caller-side discharge of the backward returned by
/// `return_mut_guard_no_release`.
#[verify::stateful_lifetimes]
pub fn caller_releases_mut_guard(lock: &mut Lock) {
    let guard = return_mut_guard_no_release(lock);
    release_mut(guard);
}

// ---------------------------------------------------------------------------
// Scenario 2: guard moved into a callee that consumes it by value.
// ---------------------------------------------------------------------------

#[verify::stateful_lifetimes]
pub fn move_guard_into_callee(lock: &Lock) -> u32 {
    let g = acquire(lock);
    consume_guard(g)
}

// ---------------------------------------------------------------------------
// Scenario 3: guard consumed by a dedicated (non-opaque) helper function.
// ---------------------------------------------------------------------------

#[verify::stateful_lifetimes]
fn consume_and_report(g: Guard<'_>) -> u32 {
    consume_guard(g)
}

#[verify::stateful_lifetimes]
pub fn call_consume_and_report(lock: &Lock) -> u32 {
    let g = acquire(lock);
    consume_and_report(g)
}

// ---------------------------------------------------------------------------
// Scenario 4: early return with a guard from inside an `if`.
// ---------------------------------------------------------------------------

#[verify::stateful_lifetimes]
pub fn early_return_with_guard(lock: &Lock, take_early: bool) -> Guard<'_> {
    if take_early {
        return acquire(lock);
    }
    acquire(lock)
}

// ---------------------------------------------------------------------------
// Scenario 5: guard returned from different `match` branches.
// ---------------------------------------------------------------------------

#[verify::stateful_lifetimes]
pub fn branch_match_guard(lock: &Lock, mode: u8) -> Guard<'_> {
    match mode {
        0 => acquire(lock),
        1 => {
            let g = acquire(lock);
            g
        }
        _ => acquire(lock),
    }
}

// ---------------------------------------------------------------------------
// Scenario 6: guard threaded through `Option::?`.
// ---------------------------------------------------------------------------

#[verify::stateful_lifetimes]
pub fn option_try_guard(maybe_lock: Option<&Lock>) -> Option<Guard<'_>> {
    let lock = maybe_lock?;
    Some(acquire(lock))
}

// ---------------------------------------------------------------------------
// Scenario 7: guard threaded through `Result::?`.
// ---------------------------------------------------------------------------

#[verify::stateful_lifetimes]
pub fn result_try_guard(maybe_lock: Result<&Lock, u32>) -> Result<Guard<'_>, u32> {
    let lock = maybe_lock?;
    Ok(acquire(lock))
}

// ---------------------------------------------------------------------------
// Scenarios 8-9: nested (non-opaque) helper returning a guard, two levels
// of indirection.
// ---------------------------------------------------------------------------

#[verify::stateful_lifetimes]
fn inner_acquire_helper(lock: &Lock) -> Guard<'_> {
    acquire(lock)
}

#[verify::stateful_lifetimes]
pub fn outer_nested_helper(lock: &Lock) -> Guard<'_> {
    inner_acquire_helper(lock)
}

// ---------------------------------------------------------------------------
// Scenario 10: guard returned wrapped inside an `Option`.
// ---------------------------------------------------------------------------

#[verify::stateful_lifetimes]
pub fn guard_in_option(lock: &Lock, present: bool) -> Option<Guard<'_>> {
    if present {
        Some(acquire(lock))
    } else {
        None
    }
}

// ---------------------------------------------------------------------------
// Scenario 11: guard returned wrapped inside a `Result`.
// ---------------------------------------------------------------------------

/// EXPECTED type shape: `Result (core.result.Result Guard u32)` — note the
/// two distinct levels here. The *outer* `Result` is Aeneas' own effect
/// monad (`ok` / `fail` / `div`); the *inner* `core.result.Result` is the
/// translation of Rust's `Result<Guard, u32>` type, an ordinary two-
/// constructor inductive (`Ok` / `Err`). Taking the `ok: false` branch below
/// does **not** produce an Aeneas `fail` — it produces
/// `ok (core.result.Result.Err 0xDEAD)`, a perfectly ordinary *successful*
/// outcome of the outer effect monad that merely carries an `Err` value at
/// the Rust level. Conflating "the function returned `Err`" with "the
/// function's translation failed (`fail`)" is a common but incorrect
/// reading of this shape; see [`call_acquire_with_status`] (Scenario 20)
/// for the same point in the context of `?`-propagation.
#[verify::stateful_lifetimes]
pub fn guard_in_result(lock: &Lock, ok: bool) -> Result<Guard<'_>, u32> {
    if ok {
        Ok(acquire(lock))
    } else {
        Err(0xDEAD)
    }
}

// ---------------------------------------------------------------------------
// Scenario 12: guard returned wrapped inside a tuple, alongside a scalar.
// ---------------------------------------------------------------------------

#[verify::stateful_lifetimes]
pub fn guard_in_tuple(lock: &Lock) -> (Guard<'_>, u32) {
    let g = acquire(lock);
    (g, 42u32)
}

// ---------------------------------------------------------------------------
// Scenario 13: guard replaced before return — the first guard is shadowed
// (and, since `Guard` is opaque, silently never released); the second guard
// is what actually gets returned.
// ---------------------------------------------------------------------------

#[verify::stateful_lifetimes('a)]
pub fn replace_guard_before_return<'a>(first: &'a Lock, second: &'a Lock) -> Guard<'a> {
    let _g1 = acquire(first);
    let g2 = acquire(second);
    g2
}

// ---------------------------------------------------------------------------
// Scenario 14: closure body returns a guard normally; the closure is
// created and immediately called once.
//
// This scenario has been moved to
// `lt-stateful-return-closure-known-failures.rs`: today Aeneas errors out
// trying to end an
// abstraction it has itself marked as non-endable while translating the
// closure's synthesized `call` operator, so `closure_returns_guard` cannot
// currently be included here as a fixture that "just translates".
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// Scenario 15: `if`/`else` as a tail expression — a "normal" (non-`return`)
// return path.
// ---------------------------------------------------------------------------

#[verify::stateful_lifetimes]
pub fn if_expr_tail_guard(lock: &Lock, left: bool) -> Guard<'_> {
    if left {
        acquire(lock)
    } else {
        acquire(lock)
    }
}

// ---------------------------------------------------------------------------
// Scenario 16: `match` as a tail expression — another "normal" return path.
// ---------------------------------------------------------------------------

#[verify::stateful_lifetimes]
pub fn match_expr_tail_guard(lock: &Lock, mode: u8) -> Guard<'_> {
    match mode {
        0 => acquire(lock),
        _ => acquire(lock),
    }
}

// ---------------------------------------------------------------------------
// Scenario 17: guard produced after unrelated local scalar computation — a
// fully "normal" return path with no early exits, branching, or wrapping.
// ---------------------------------------------------------------------------

#[verify::stateful_lifetimes]
pub fn guard_after_computation(lock: &Lock, x: u32) -> (Guard<'_>, u32) {
    let y = x.wrapping_add(1);
    (acquire(lock), y)
}

// ---------------------------------------------------------------------------
// Scenario 18: guard escapes a `loop` via `break` with a value — a genuine,
// multi-iteration loop (see the module-level "Note on the original
// `loop { break .. }` scenario" above for why the single-iteration version
// this replaces was an inadequate, effectively-erased stress test).
// ---------------------------------------------------------------------------

/// CURRENT BASELINE: Aeneas recognizes the real back-edge, but factors the
/// unique `acquire` after the generated `Result Unit` loop. This is a
/// normalization control, not the fixture that proves a guard can flow
/// through the loop result; `nested_match_real_loop_return` below is the
/// stronger case.
#[verify::stateful_lifetimes]
pub fn loop_break_with_guard(lock: &Lock, retries: u32) -> Guard<'_> {
    let mut count = 0u32;
    loop {
        if count >= retries {
            break acquire(lock);
        }
        count += 1;
    }
}

// ---------------------------------------------------------------------------
// Scenario 19: guard returned through a doubly-nested `Option`, chaining
// `?` through both layers — stresses monadic threading of an opaque
// stateful value through nested optionality.
// ---------------------------------------------------------------------------

#[verify::stateful_lifetimes]
pub fn nested_option_try_guard(maybe_lock: Option<Option<&Lock>>) -> Option<Guard<'_>> {
    let inner = maybe_lock??;
    Some(acquire(inner))
}

// ---------------------------------------------------------------------------
// Scenario 20: guard obtained via a helper whose own return type mixes a
// guard with a `Result`-wrapped scalar-shaped error, then re-wrapped by the
// caller via `?`.
// ---------------------------------------------------------------------------

#[verify::stateful_lifetimes]
fn acquire_with_status(lock: &Lock, ok: bool) -> Result<Guard<'_>, u32> {
    if ok {
        Ok(acquire(lock))
    } else {
        Err(1)
    }
}

/// EXPECTED: `acquire_with_status`'s `Err(1)` branch translates to
/// `ok (core.result.Result.Err 1)`, a normal outer-`ok` outcome (see
/// Scenario 11 above for why this is *not* an Aeneas `fail`). The `?` here
/// desugars via the `core::ops::Try` trait — schematically
/// `core.result.Result.Insts.CoreOpsTry.branch` to inspect the value,
/// followed by `core.result.Result.Insts...from_residual` on the early-exit
/// path — so `call_acquire_with_status` itself also returns
/// `ok (core.result.Result.Err 1)` on that path: the "propagation" is
/// ordinary data flow through the outer `ok`, never a `fail`/`div` case of
/// the effect monad.
#[verify::stateful_lifetimes]
pub fn call_acquire_with_status(lock: &Lock, ok: bool) -> Result<Guard<'_>, u32> {
    let g = acquire_with_status(lock, ok)?;
    Ok(g)
}

// ---------------------------------------------------------------------------
// Scenario 21: guard returned after being merely peeked at (shared borrow
// used, then the owned guard is still returned) — exercises a `&Guard`
// borrow that does not outlive the function alongside the owned guard that
// does.
// ---------------------------------------------------------------------------

#[verify::stateful_lifetimes]
pub fn peek_then_return_guard(lock: &Lock) -> Guard<'_> {
    let g = acquire(lock);
    let _snapshot = peek(&g);
    g
}

// ---------------------------------------------------------------------------
// Scenario 22: nested `match` inside a genuinely-iterating `loop`, escaping
// via `break` from a nested match arm.
// ---------------------------------------------------------------------------

/// EXPECTED: exercises the combination of a real (multi-iteration) loop
/// with a nested `match` inside its body — the `break` that ends the loop
/// sits inside one arm of that nested match, not directly in the loop
/// body. The generated loop body has two match arms; each either continues
/// or returns a guard depending on its own counter test. Unlike
/// `loop_break_with_guard`, the guard remains in the loop's `ControlFlow`
/// result and cannot be factored into one post-loop acquire.
#[verify::stateful_lifetimes]
pub fn nested_match_real_loop_return(lock: &Lock, mode: u8, iterations: u32) -> Guard<'_> {
    let mut count = 0u32;
    loop {
        match mode {
            0 => {
                if count >= iterations {
                    break acquire(lock);
                }
                count += 1;
            }
            _ => {
                count += 1;
                if count >= iterations {
                    break acquire(lock);
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Scenario 23: mutable guard escapes the genuinely-iterating nested-match
// loop, carrying a real backward obligation.
// ---------------------------------------------------------------------------

/// EXPECTED: the loop result carries both `MutGuard` and its
/// `MutGuard -> Lock` backward. Labelled breaks across two live loops are
/// covered separately as known failures in
/// `lt-stateful-labelled-{break,return}-known-failures.rs`.
#[verify::stateful_lifetimes]
pub fn nested_match_real_loop_return_mut(
    lock: &mut Lock,
    mode: u8,
    iterations: u32,
) -> MutGuard<'_> {
    let mut count = 0u32;
    loop {
        match mode {
            0 => {
                if count >= iterations {
                    break acquire_mut(lock);
                }
                count += 1;
            }
            _ => {
                count += 1;
                if count >= iterations {
                    break acquire_mut(lock);
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Scenario 24: guard release performed by the *callee* — the guard never
// escapes to the caller at all.
// ---------------------------------------------------------------------------

/// EXPECTED release discipline: **callee releases**. The guard is acquired
/// and released entirely inside this function; only a plain scalar crosses
/// the function boundary. Contrast with [`caller_releases_guard`]
/// (Scenario 25), where the release obligation is instead handed to the
/// caller.
#[verify::stateful_lifetimes]
pub fn callee_releases_guard(lock: &Lock) -> u32 {
    let g = acquire(lock);
    release(g);
    42
}

// ---------------------------------------------------------------------------
// Scenario 25: guard release left to the *caller* — the guard escapes this
// function untouched, exactly like [`return_guard_no_release`] (Scenario 1),
// but named here to sit next to [`callee_releases_guard`] for direct
// contrast between the two release disciplines.
// ---------------------------------------------------------------------------

/// EXPECTED release discipline: **caller releases**. Nothing in this
/// function calls `release`; the returned `Guard<'_>` is the caller's
/// responsibility. Since `Guard` is opaque with no `Drop` glue, nothing
/// today enforces that the caller actually does so — the point of this
/// pair is purely to give the two disciplines (Scenario 24 vs. this one)
/// distinct, self-describing names for when a future
/// `#[verify::stateful_lifetimes]` pass needs release-obligation fixtures.
#[verify::stateful_lifetimes]
pub fn caller_releases_guard(lock: &Lock) -> Guard<'_> {
    acquire(lock)
}

// ---------------------------------------------------------------------------
// Scenario 26: explicit, symmetric cleanup in *both* arms of an `if` — each
// arm acquires its own guard and releases it itself before the join,
// exercising explicit release controls rather than leaking either arm's
// guard past the branch.
// ---------------------------------------------------------------------------

/// EXPECTED: both arms are structurally parallel: acquire, do some
/// (opaque) work while holding the guard, then `release` explicitly before
/// the `if` join. No guard value is ever live across the join point, so —
/// unlike [`replace_guard_before_return`] (Scenario 13), where the first
/// guard is silently shadowed and never released — this function
/// demonstrates the fully-cleaned-up alternative: every path releases
/// exactly the guard it acquired, in the same arm, before the merge.
#[verify::stateful_lifetimes]
pub fn manual_cleanup_both_arms(lock_a: &Lock, lock_b: &Lock, left: bool) -> u32 {
    if left {
        let g = acquire(lock_a);
        let v = consume_guard(g);
        v
    } else {
        let g = acquire(lock_b);
        release(g);
        0
    }
}

// ---------------------------------------------------------------------------
// Scenario 27: guard returned wrapped inside `Result<Option<Guard<'_>>, E>`
// — composing both wrapper shapes (Scenario 10's `Option` and Scenario 11's
// `Result`) in a single return type.
// ---------------------------------------------------------------------------

/// EXPECTED type shape: `Result (core.result.Result (Option Guard) u32)`.
/// As in Scenario 11, the outer `Result` is Aeneas' effect monad and stays
/// `ok` on every path below — including the `Err` path, which is
/// `ok (core.result.Result.Err 0xBEEF)`, and the `Ok(None)` path, which is
/// `ok (core.result.Result.Ok Option.none)`. No path here ever produces an
/// Aeneas `fail`.
#[verify::stateful_lifetimes]
pub fn guard_in_result_option(lock: &Lock, mode: u8) -> Result<Option<Guard<'_>>, u32> {
    match mode {
        0 => Ok(Some(acquire(lock))),
        1 => Ok(None),
        _ => Err(0xBEEF),
    }
}
