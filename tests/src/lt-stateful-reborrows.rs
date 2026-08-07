//@ [!lean] skip
//! EXPECTED AFTER IMPLEMENTATION:
//! This file complements `lt-stateful-signatures.rs` and focuses on
//! *reborrows* under the future "stateful lifetimes" feature: nested field
//! projections through a guard, chains of reborrows, and interactions
//! between stateful and ordinary lifetimes across nested calls. See
//! `lt-stateful-signatures.rs` for the module-level definition of bare-vs-
//! named attribute semantics (bare marks every lifetime parameter of the
//! function as stateful; named marks only the listed ones; the attribute's
//! complete absence means no lifetime is stateful). Once implemented,
//! `#[verify::stateful_lifetimes]` (or the explicit
//! `#[verify::stateful_lifetimes('a)]` form) is expected to translate:
//!   - `WriteGuard::get_mut()` on a field/subfield path (e.g.
//!     `guard.get_mut().field`) to a single setter backward function
//!     `FieldType -> Result Guard`, composed with the ordinary field-update
//!     translation Aeneas already performs for plain `&mut` projections.
//!   - A chain of reborrows of the *same* guard (e.g. `get_mut()` called in
//!     several disjoint scopes, or through an intervening `&mut WriteGuard`
//!     reference) to produce one setter/outer-region pair per call, threaded
//!     in program order. Reborrowing must not merge calls or duplicate a
//!     call's region components.
//!   - A shared borrow taken from an *unrelated* lock/value while a write
//!     guard is held elsewhere to be entirely independent: the pure shared
//!     borrow gets no backward function, the write guard still gets its one
//!     setter plus its release.
//!   - Lifetime SCC/outlives constraints among multiple stateful lifetimes
//!     (e.g. `'a: 'b`) to be resolved the same way region groups are
//!     resolved today for ordinary borrows, before the guard/release
//!     bookkeeping is layered on top. When a stateful lifetime and an
//!     ordinary lifetime are related by an outlives constraint (as in
//!     `outlives_chain` below), only the lifetime that is actually tied to
//!     the resource acquisition carries the release obligation -- the
//!     obligation is not duplicated onto every named lifetime that happens
//!     to appear in the outlives chain (see "OBLIGATION TRANSFER" on
//!     `outlives_chain` below for the precise rule).
//!   - Ordinary local `&mut` reborrows that never touch a `Lock`/`Guard`
//!     (plain field projections, the classic `choose` pattern, chains of
//!     reborrowing helper calls) to remain byte-for-byte the same *pure*
//!     backward-function translation Aeneas produces today: this feature
//!     must be a strict extension, not a regression, for code with no
//!     stateful lifetimes at all. Such functions carry NO
//!     `#[verify::stateful_lifetimes]` attribute at all (the attribute's
//!     complete absence, not the bare form -- see the semantics note above),
//!     since tagging code that never acquires a resource would misstate
//!     what the attribute means.
//!
//! CURRENT BASELINE:
//! `#[verify::stateful_lifetimes]` / `#[verify::stateful_lifetimes('a)]` are
//! not yet recognized by Aeneas. As documented in `lt-stateful-signatures.rs`,
//! `rustc` accepts them silently as an inert tool attribute (via
//! `#![register_tool(verify)]`), but Charon's attribute parser does
//! recognize the `verify::` prefix, fails to match `stateful_lifetimes`
//! against any known attribute name, and reports a non-fatal warning
//! before continuing as if the attribute were absent -- rustc is silent,
//! Charon warns. `Lock`, `ReadGuard`, and `WriteGuard` are
//! `#[verify::opaque]`, so every method call on them is extracted as an
//! opaque call under the existing translation; the plain (non-lock)
//! functions at the bottom of this file already exercise today's ordinary
//! backward-function machinery and are included as no-regression fixtures.
//!
//! Calling `get_mut()` through a borrowed `&mut WriteGuard` currently loses
//! a given-back value; its minimal reproducer lives in
//! `lt-stateful-reborrow-mut-known-failures.rs`. A separate backend bug
//! involving checked arithmetic embedded directly in a `get_mut` assignment
//! lives in `lt-stateful-reborrow-shared-known-failures.rs`; the correctly
//! hoisted shared-reborrow variant is included below.
#![feature(register_tool)]
#![register_tool(verify)]

use std::marker::PhantomData;

#[verify::opaque]
pub struct Lock<T> {
    _marker: PhantomData<T>,
}

#[verify::opaque]
pub struct ReadGuard<'a, T> {
    _marker: PhantomData<&'a T>,
}

#[verify::opaque]
pub struct WriteGuard<'a, T> {
    _marker: PhantomData<&'a mut T>,
}

impl<T> Lock<T> {
    #[verify::opaque]
    pub fn new(_value: T) -> Self {
        unimplemented!()
    }

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

    #[verify::stateful_lifetimes]
    #[verify::opaque]
    pub fn release(self) {}
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

    #[verify::stateful_lifetimes]
    #[verify::opaque]
    pub fn release(self) {}
}

/// A plain (non-opaque) struct with two fields, used to exercise field and
/// subfield reborrows through a guard.
pub struct Pair {
    pub a: i32,
    pub b: i32,
}

/// A struct nesting a `Pair`, used to exercise *subfield* (two-level)
/// reborrows through a guard.
pub struct Nested {
    pub pair: Pair,
    pub tag: bool,
}

/// A struct nesting a `Lock`, used to exercise a lock reached *through* a
/// guard's field projection (a "lock inside a lock").
pub struct Cabinet {
    pub inner: Lock<i32>,
}

/// Field reborrow through a write guard: `guard.get_mut().a = ...`.
/// EXPECTED: one setter backward for the whole `Pair`, plus the call's
/// outer-region backward, composed with ordinary field-update logic.
#[verify::stateful_lifetimes]
pub fn field_reborrow_write_guard(lock: &Lock<Pair>) {
    let mut guard = lock.write();
    guard.get_mut().a = 10;
    guard.release();
}

/// Two disjoint subfield setters through a SINGLE `get_mut()` call: `.a`
/// and `.b` are both written through the same `&mut Pair` returned by one
/// call (as opposed to `repeated_deref_mut_chain` below, which calls
/// `get_mut()` twice). EXPECTED: exactly one setter plus one outer-region
/// backward for this call, composed with Aeneas's existing disjoint-field
/// update handling for `.a` and `.b`.
#[verify::stateful_lifetimes]
pub fn disjoint_subfield_setters_single_get_mut(lock: &Lock<Pair>) {
    let mut guard = lock.write();
    let pair = guard.get_mut();
    pair.a = 1;
    pair.b = 2;
    guard.release();
}

/// Subfield reborrow (two levels deep) through a write guard:
/// `guard.get_mut().pair.b = ...`. EXPECTED: still one setter plus one
/// outer-region backward for the top-level `Nested` value.
#[verify::stateful_lifetimes]
pub fn subfield_reborrow_nested(lock: &Lock<Nested>) {
    let mut guard = lock.write();
    guard.get_mut().pair.b = 20;
    guard.release();
}

/// `get_mut()` called on the same guard in two disjoint scopes. EXPECTED:
/// two setter/outer-region pairs, one per call, sequenced through the guard.
#[verify::stateful_lifetimes]
pub fn repeated_deref_mut_chain(lock: &Lock<Pair>) {
    let mut guard = lock.write();
    {
        let r1 = guard.get_mut();
        r1.a += 1;
    }
    {
        let r2 = guard.get_mut();
        r2.b += 1;
    }
    guard.release();
}

fn peek_pair_via_shared_guard(guard: &WriteGuard<'_, Pair>) -> i32 {
    guard.get().a
}

/// A shared reborrow helper followed by a mutable update. Hoisting the
/// checked addition before the `get_mut` place keeps the dynamic check
/// reconstruction intact and translates successfully.
#[verify::stateful_lifetimes]
pub fn shared_reborrow_then_hoisted_update(lock: &Lock<Pair>) -> i32 {
    let mut guard = lock.write();
    let peeked = peek_pair_via_shared_guard(&guard);
    let updated = peeked + 1;
    guard.get_mut().b = updated;
    let result = guard.get().b;
    guard.release();
    result
}

/// Nested lock through a guard: acquire the outer lock, project through
/// the outer guard's `get_mut` to the `inner` field (an ordinary,
/// non-stateful field projection), then acquire and release the INNER
/// lock reached through that projection. EXPECTED: two independent
/// guard/release pairs -- one for the outer `Cabinet` guard (whose setter
/// backward function threads the still-locked, unmodified
/// `inner: Lock<i32>` field back through) and one for the inner `i32`
/// guard (its own acquire/get/release) -- entirely nested inside the
/// outer guard's lifetime.
#[verify::stateful_lifetimes]
pub fn nested_lock_through_guard(outer_lock: &Lock<Cabinet>) -> i32 {
    let mut outer_guard = outer_lock.write();
    let inner_guard = outer_guard.get_mut().inner.read();
    let value = *inner_guard.get();
    inner_guard.release();
    outer_guard.release();
    value
}

/// Ordinary (non-lock) mutable sub-borrow returned from a function: no guard
/// involved at all. No-regression fixture: this function never acquires a
/// guard, so it carries NO `#[verify::stateful_lifetimes]` attribute (see
/// the module docs above), keeping today's plain backward-function
/// translation for `&mut i32` tied to `'a`.
pub fn returning_mutable_sub_borrow<'a>(pair: &'a mut Pair) -> &'a mut i32 {
    &mut pair.a
}

/// Identity-like helper used to build a reborrow chain below.
fn identity_mut<'a, T>(x: &'a mut T) -> &'a mut T {
    x
}

/// A chain of reborrows through a helper function before projecting a
/// field. No-regression fixture: this never touches a `Lock`/`Guard`, so
/// it carries NO `#[verify::stateful_lifetimes]` attribute and keeps the
/// existing pure backward-function chain, entirely unaffected by stateful
/// lifetimes.
pub fn reborrow_chain_through_helper<'a>(pair: &'a mut Pair) -> &'a mut i32 {
    let p1 = identity_mut(pair);
    let p2 = identity_mut(p1);
    &mut p2.a
}

/// A shared borrow of an unrelated value taken while a write guard is held.
/// EXPECTED: the shared borrow of `other` gets no backward function at all
/// (as usual for shared borrows), independent of the guard's own setter and
/// release backward functions.
#[verify::stateful_lifetimes]
pub fn shared_borrow_during_write_guard(lock: &Lock<Pair>, other: &i32) -> i32 {
    let mut guard = lock.write();
    guard.get_mut().a = *other;
    let extra = *other;
    guard.release();
    extra
}

/// Lifetime outlives constraint (`'b: 'a`) between a *stateful* lifetime
/// `'b` and an *ordinary* lifetime `'a`, where a guard acquired under the
/// stateful borrow `'b` is returned with the ordinary lifetime `'a` via
/// covariant subtyping (see `read_guard_covariance` in
/// `lt-stateful-signatures.rs`). Only `'b` -- the lifetime actually tied to
/// the `Lock` borrow that produces the guard -- is named as stateful:
/// `'a` is never associated with any acquire operation, so it must NOT be
/// marked stateful and must NOT receive its own, second release
/// obligation. (An earlier version of this fixture marked both `'a` and
/// `'b` as stateful, which double-counted the release obligation onto a
/// lifetime that never acquires anything; this is the corrected form.)
///
/// OBLIGATION TRANSFER: because Rust allows returning a `ReadGuard<'b, T>`
/// wherever a `ReadGuard<'a, T>` is expected (by covariant subtyping, given
/// `'b: 'a`), the guard's single release obligation must be resolved
/// against the SAME underlying region-group representative that ordinary
/// (non-stateful) borrow-checking already computes for the `{'a, 'b}`
/// outlives chain. EXPECTED: the stateful lifetimes pass must run
/// region/SCC resolution first, exactly as for ordinary borrows, determine
/// that `'b` is the resource-owning representative of that chain, and only
/// then attach the guard/release bookkeeping to that representative -- it
/// must NOT independently track one obligation per named lifetime that
/// happens to appear in the outlives chain.
#[verify::stateful_lifetimes('b)]
pub fn outlives_chain<'a, 'b: 'a, T>(lock: &'b Lock<T>) -> ReadGuard<'a, T> {
    lock.read()
}

/// Helper that requires two read guards to share a single lifetime `'c`.
/// Calling it with guards drawn from *different* input lifetimes forces
/// the borrow checker to compute `'c` as a genuine meet of those input
/// lifetimes (using `ReadGuard`'s covariance -- see `read_guard_covariance`
/// in `lt-stateful-signatures.rs`) for the duration of the call.
fn same_lifetime_read_pair<'c, T>(
    g1: ReadGuard<'c, T>,
    g2: ReadGuard<'c, T>,
) -> (ReadGuard<'c, T>, ReadGuard<'c, T>) {
    (g1, g2)
}

/// A *real* region-group/SCC fixture: `ga` and `gb` are drawn from two
/// independent locks (`'a` and `'b` have no declared relationship between
/// them), but the call to `same_lifetime_read_pair` forces the borrow
/// checker to find a common region `'c` that both `'a` and `'b` outlive
/// for the duration of the call -- a genuine merge of two otherwise
/// unrelated region groups. (An earlier version of this fixture declared a
/// vacuous `'a: 'b` bound that was never actually used by any shared type
/// or expression in the function body, so the borrow checker's region/SCC
/// resolution had nothing real to do; this version replaces it with a
/// call site that genuinely requires merging the two regions.) EXPECTED:
/// the stateful lifetimes pass must perform this same region/SCC
/// resolution -- exactly as ordinary borrow-checking does -- to determine
/// the shape of the merge at the `same_lifetime_read_pair` call site, and,
/// independently of that merge, must still produce exactly TWO release
/// obligations, one per guard: the SCC merge affects lifetime bookkeeping
/// at the call site, not how many distinct guards/releases exist.
#[verify::stateful_lifetimes('a, 'b)]
pub fn scc_two_guards<'a, 'b, T: Copy>(lock_a: &'a Lock<T>, lock_b: &'b Lock<T>) -> (T, T) {
    let ga = lock_a.read();
    let gb = lock_b.read();
    let (ga, gb) = same_lifetime_read_pair(ga, gb);
    let a_val = *ga.get();
    let b_val = *gb.get();
    ga.release();
    gb.release();
    (a_val, b_val)
}

/// The classic `choose` pattern (see `paper.rs`), with no lock involved at
/// all. No-regression fixture: EXPECTED to keep exactly today's backward
/// function `T -> (T, T)` (picking which of `x`/`y` gets the update).
pub fn choose<'a, T>(b: bool, x: &'a mut T, y: &'a mut T) -> &'a mut T {
    if b {
        x
    } else {
        y
    }
}

/// `choose` combined with field projection: still no lock involved.
/// No-regression fixture: this never touches a `Lock`/`Guard`, so it
/// carries NO `#[verify::stateful_lifetimes]` attribute and keeps today's
/// plain backward-function translation, projecting into whichever field of
/// `x`/`y` was chosen.
pub fn choose_field_projection<'a>(b: bool, x: &'a mut Pair, y: &'a mut Pair) -> &'a mut i32 {
    if b {
        &mut x.a
    } else {
        &mut y.b
    }
}

/// A plain helper taking an ordinary local `&mut i32`.
pub fn local_mut_increment(x: &mut i32) {
    *x += 1;
}

/// Ordinary local `&mut` reborrow across a helper call, with no lock
/// anywhere in sight. No-regression fixture: this never touches a
/// `Lock`/`Guard`, so it carries NO `#[verify::stateful_lifetimes]`
/// attribute and remains a pure backward-function translation, entirely
/// unaffected by the stateful lifetimes feature.
pub fn local_reborrow_pure<'a>(x: &'a mut i32) -> &'a mut i32 {
    local_mut_increment(x);
    x
}
