//@ [!lean] skip
//@ [lean] aeneas-args=-stateful-lifetimes -eval-drops
#![feature(register_tool)]
#![register_tool(verify)]
#![allow(dead_code, unused_variables, unused_mut)]

//! # Optimizer-hostile stateful fixtures
//!
//! Aeneas' micro-passes were designed for a pipeline in which every value is
//! pure and the `Result` monad only tracks partiality.  A stateful backward
//! function breaks that assumption: it is a genuine effect, so it may not be
//! deleted, duplicated, hoisted, sunk, or merged with another one.
//!
//! Each function below is bait for one specific pass.  The companion file
//! `tests/lean/LtStatefulOptimizerCheck.lean` pins the expected output with
//! `rfl`, so a pass that eats an acquisition or a release turns into a build
//! failure instead of a silently weaker model.
//!
//! The reason this matters: when a release is emitted as
//! `let () := release_fn guard` — a **pure** application — then
//!
//!   * `filter_useless` deletes it, because it binds an unused `()` in a
//!     non-monadic let;
//!   * `unit_vars_to_unit` rewrites the binder away;
//!   * `simplify_duplicate_calls` may merge two of them.
//!
//! Emitting `release_fn guard : Result Unit` and binding it monadically makes
//! all three passes leave it alone, because `texpr_cannot_fail` is false for a
//! function application.  These fixtures are what proves that claim.

use std::marker::PhantomData;

#[verify::opaque]
pub struct Lock<T> {
    marker: PhantomData<T>,
}

#[verify::opaque]
pub struct ReadGuard<'a, T> {
    marker: PhantomData<&'a T>,
}

#[verify::opaque]
pub struct WriteGuard<'a, T> {
    marker: PhantomData<&'a mut T>,
}

impl<T> Lock<T> {
    #[verify::stateful_lifetimes]
    #[verify::opaque]
    pub fn read(&self) -> ReadGuard<'_, T> {
        unimplemented!()
    }

    #[verify::stateful_lifetimes]
    #[verify::opaque]
    pub fn write(&self) -> WriteGuard<'_, T> {
        unimplemented!()
    }
}

impl<'a, T> ReadGuard<'a, T> {
    #[verify::opaque]
    pub fn get(&self) -> &T {
        unimplemented!()
    }
}

impl<'a, T> WriteGuard<'a, T> {
    #[verify::opaque]
    pub fn get(&self) -> &T {
        unimplemented!()
    }

    #[verify::stateful_lifetimes]
    #[verify::opaque]
    pub fn get_mut(&mut self) -> &mut T {
        unimplemented!()
    }
}

// ---------------------------------------------------------------------------
// Bait for `filter_useless`
// ---------------------------------------------------------------------------

/// The release binds `()`, that `()` is never used, and the function keeps
/// computing afterwards. `filter_useless` removes a non-monadic let whose
/// pattern is all dummies, so under the pure-application encoding this release
/// disappears entirely and the lock is never given back.
///
/// EXPECTED: one `Lock.read`, one release, then `ok 7#i32`.
pub fn release_result_unused(lock: &Lock<i32>) -> i32 {
    {
        let guard = lock.read();
        let _ = *guard.get();
    }
    7
}

/// Same, but the guard is a write guard and its payload is written first, so
/// the release argument is the *updated* guard. If the setter is dropped as
/// "useless" the release would receive a stale guard.
///
/// EXPECTED: `get_mut`, setter, outer, release, then `ok 0#i32`.
pub fn release_after_write_unused(lock: &Lock<i32>) -> i32 {
    {
        let mut guard = lock.write();
        *guard.get_mut() = 5;
    }
    0
}

// ---------------------------------------------------------------------------
// Bait for `simplify_duplicate_calls`
// ---------------------------------------------------------------------------

/// Two *syntactically identical* acquisitions of the same lock. CSE would merge
/// `Lock.read lock` into a single call, turning two acquisitions into one — and
/// with it two releases into one. Acquisition is an effect; it may not be
/// shared.
///
/// EXPECTED: exactly two `Lock.read lock` calls and two releases.
pub fn acquire_same_lock_twice(lock: &Lock<i32>) -> i32 {
    let first = {
        let guard = lock.read();
        *guard.get()
    };
    let second = {
        let guard = lock.read();
        *guard.get()
    };
    first + second
}

/// Two identical writes of the same constant through two separate guards on the
/// same lock. Both the acquisitions and the setter applications are
/// syntactically identical, which is the worst case for CSE.
///
/// EXPECTED: two `Lock.write lock` calls, two setters, two releases.
pub fn write_same_constant_twice(lock: &Lock<i32>) {
    {
        let mut guard = lock.write();
        *guard.get_mut() = 1;
    }
    {
        let mut guard = lock.write();
        *guard.get_mut() = 1;
    }
}

// ---------------------------------------------------------------------------
// Bait for `unit_vars_to_unit`
// ---------------------------------------------------------------------------

/// A lock whose payload is `()`. Every value flowing through the guard is unit,
/// so a pass that rewrites unit-typed binders to `()` can erase the write-back
/// and, under the pure encoding, the release with it.
///
/// EXPECTED: `Lock.write`, `get_mut`, setter, outer, release.
pub fn write_unit_payload(lock: &Lock<()>) {
    let mut guard = lock.write();
    *guard.get_mut() = ();
}

// ---------------------------------------------------------------------------
// Conditionality: an effect behind a branch must stay behind it
// ---------------------------------------------------------------------------

/// The lock is acquired only when `take` holds. Hoisting the acquisition out of
/// the branch would make the program take the lock unconditionally.
///
/// EXPECTED: `Lock.read` and its release occur only in the `then` branch.
pub fn conditional_acquire(lock: &Lock<i32>, take: bool) -> i32 {
    if take {
        let guard = lock.read();
        *guard.get()
    } else {
        0
    }
}

/// Both branches acquire, but from *different* locks. Merging the two branches
/// into one acquisition would lock the wrong object on one path.
///
/// EXPECTED: `Lock.read first` in one branch, `Lock.read second` in the other.
pub fn branch_acquires_different_locks(
    first: &Lock<i32>,
    second: &Lock<i32>,
    use_first: bool,
) -> i32 {
    if use_first {
        let guard = first.read();
        *guard.get()
    } else {
        let guard = second.read();
        *guard.get()
    }
}

// ---------------------------------------------------------------------------
// Multiplicity: an effect inside a loop runs once per iteration
// ---------------------------------------------------------------------------

/// Acquire and release once per iteration. Hoisting the acquisition out of the
/// loop would hold the lock across all iterations instead of taking it `count`
/// times.
///
/// EXPECTED: the acquisition and the release are both inside the loop body.
pub fn acquire_in_loop(lock: &Lock<i32>, count: u32) -> u32 {
    let mut total = 0;
    let mut index = 0;
    while index < count {
        let guard = lock.read();
        let _ = *guard.get();
        total += 1;
        index += 1;
    }
    total
}

// ---------------------------------------------------------------------------
// Ordering: releases follow Rust drop order
// ---------------------------------------------------------------------------

/// Three nested guards on three different locks. Rust drops them in reverse
/// declaration order, so the releases must appear third, second, first.
///
/// EXPECTED: releases for `third`, then `second`, then `first`.
pub fn three_nested_guards(first: &Lock<i32>, second: &Lock<i32>, third: &Lock<i32>) -> i32 {
    let first_guard = first.read();
    let second_guard = second.read();
    let third_guard = third.read();
    *first_guard.get() + *second_guard.get() + *third_guard.get()
}

/// An inner scope closes while an outer guard is still held, so the inner
/// release must be sequenced strictly between the outer acquisition and the
/// outer release — it may not sink to the end of the function.
///
/// EXPECTED: outer acquire, inner acquire, inner release, outer release.
pub fn inner_scope_releases_first(outer: &Lock<i32>, inner: &Lock<i32>) -> i32 {
    let outer_guard = outer.read();
    {
        let inner_guard = inner.read();
        let _ = *inner_guard.get();
    }
    *outer_guard.get()
}
