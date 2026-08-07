//@ [!lean] skip
//! EXPECTED AFTER IMPLEMENTATION:
//! This file is a pre-implementation fixture for the "stateful lifetimes"
//! feature: a way of marking that a lifetime parameter is tied to a runtime
//! resource (e.g. a lock guard) rather than a purely symbolic Rust borrow.
//! Once implemented, functions tagged `#[verify::stateful_lifetimes]` (or
//! `#[verify::stateful_lifetimes('a)]` to name the stateful lifetime(s)
//! explicitly) are expected to translate to Lean roughly as follows:
//!   - `Lock::read` / `Lock::write` acquire a resource and return a guard
//!     together with an *explicit* backward function `Guard -> Result Unit`
//!     that models `release`, i.e. giving the resource back.
//!   - `ReadGuard::get` / `WriteGuard::get` (shared deref) do **not** get a
//!     backward function: reading through a guard is a pure projection.
//!   - Aeneas emits one backward component per region in a function
//!     signature. `WriteGuard::get_mut` has the short method-borrow region
//!     and the guard's own region, so today's model has two backwards:
//!     `T -> Guard` (the setter) and `Guard -> Guard` (the outer region).
//!     Each call gets its own pair and the caller must sequence them. The
//!     stateful feature changes which applications are effectful; it must
//!     not merge distinct calls or invent a third release obligation.
//!   - Ordinary (non-stateful) `&mut` borrows, e.g. `Lock::get_mut` which
//!     bypasses the guard/release protocol entirely, keep today's plain
//!     backward-function translation unchanged.
//!   - Mixing a stateful lifetime with an ordinary ("pure") lifetime in the
//!     same signature must translate each independently: the stateful one
//!     gets the guard/release treatment, the pure one gets the usual
//!     backward function (or none, if it is a shared borrow).
//!
//! BARE-VS-NAMED ATTRIBUTE SEMANTICS (defined here, applies to every
//! `#[verify::stateful_lifetimes]` fixture in this test suite):
//!   - The bare form `#[verify::stateful_lifetimes]` (no argument) marks
//!     **every** lifetime parameter that appears in the function's own
//!     generic parameter list as stateful. This is defined to be exactly
//!     equivalent to the named form that lists all of those lifetimes
//!     explicitly, in declaration order -- e.g. on a signature with a
//!     single lifetime parameter, bare and `('a)` (where `'a` is that
//!     parameter's name) must translate identically; see
//!     `minimal_write_acquire_release` / `minimal_write_acquire_release_named`
//!     below for a worked example.
//!   - The named form `#[verify::stateful_lifetimes('a, 'b, ...)]` marks
//!     only the listed lifetime(s) as stateful. Any other lifetime
//!     parameter present in the signature but *not* listed remains an
//!     ordinary ("pure") lifetime, translated exactly as today (see
//!     `mixed_stateful_and_pure` below).
//!   - Elided/anonymous lifetimes (e.g. `&Lock<T>` in a bare-form
//!     signature) count as lifetime parameters of the function for the
//!     purposes of the bare form, exactly as if they had been written out
//!     with an explicit name.
//!   - A lifetime introduced by a method's surrounding `impl` binder and
//!     occurring in the method signature counts for both forms: bare marks
//!     it (in impl-binder order, before method-local/elided lifetimes), and
//!     named form may list it explicitly. Thus bare `WriteGuard::get_mut`
//!     marks both the guard's outer `'a` and the elided `&mut self` region.
//!   - The complete absence of the attribute (no `#[verify::stateful_lifetimes]`
//!     at all) is a third, distinct case: it means no lifetime in the
//!     signature is stateful, and the function is translated exactly as it
//!     is today, with no guard/release reasoning applied to any borrow --
//!     see `unannotated_write_acquire_release` below.
//!
//! CURRENT BASELINE:
//! `#[verify::stateful_lifetimes]` and `#[verify::stateful_lifetimes('a)]`
//! are not yet recognized as meaningful attributes by the compiler. Their
//! current handling differs between the two tools in this pipeline:
//!   - `rustc` accepts them unconditionally and silently: because `verify`
//!     is registered via `#![register_tool(verify)]`, rustc treats
//!     `verify::*` as an inert tool attribute namespace and never inspects
//!     its contents.
//!   - Charon does **not** treat it as inert: its attribute parser
//!     recognizes the `verify::` prefix specifically (the same prefix used
//!     by `#[verify::opaque]` and `#[verify::test]`), attempts to match
//!     `stateful_lifetimes` against its table of known attribute names,
//!     fails to find it, and reports a *non-fatal warning*
//!     (`Error parsing attribute: Unrecognized attribute: ...`) before
//!     continuing as if the attribute were simply absent. In short:
//!     rustc is silent, Charon warns.
//! Every function below is expected to be extracted today using the
//! *existing* translation rules regardless of this warning: `Lock`,
//! `ReadGuard`, and `WriteGuard` are `#[verify::opaque]`, so all of their
//! methods are treated as opaque calls, and no stateful/backward-release
//! reasoning is performed. This file exists so that, once the feature
//! lands, these signatures can be used (unmodified, or with minimal
//! changes) as regression fixtures for the new behavior described above.
//!
//! Important current shapes, recorded explicitly:
//! - `read : Lock T -> Result (ReadGuard T)` and `try_read` have no backward
//!   because their shared-borrow-only region is erased today.
//! - `write : Lock T -> Result (WriteGuard T × (WriteGuard T -> Unit))`.
//! - `get_mut : WriteGuard T -> Result
//!   (T × (T -> WriteGuard T) × (WriteGuard T -> WriteGuard T))`.
//! - `WriteGuard.release : WriteGuard T -> Result (WriteGuard T)` today;
//!   the future resource-release contract should instead consume the guard
//!   and perform the stateful effect.
#![feature(register_tool)]
#![register_tool(verify)]

use std::marker::PhantomData;

/// Opaque lock guarding a `T`. Conceptually similar to `std::sync::RwLock<T>`
/// but modeled abstractly (no real interior mutability) so that we get a
/// symbolic value whose methods can be marked `#[verify::opaque]`.
#[verify::opaque]
pub struct Lock<T> {
    _marker: PhantomData<T>,
}

/// Opaque read guard, tied to the lifetime of the `Lock` borrow that
/// produced it. `PhantomData<&'a T>` makes `ReadGuard` *covariant* in
/// `'a` (see `read_guard_covariance` below).
#[verify::opaque]
pub struct ReadGuard<'a, T> {
    _marker: PhantomData<&'a T>,
}

/// Opaque write guard, tied to the lifetime of the `Lock` borrow that
/// produced it. `PhantomData<&'a mut T>` makes `WriteGuard` *invariant* in
/// `'a` (see `write_guard_invariance_contrast` below), unlike `ReadGuard`.
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
    #[verify::stateful_lifetimes]
    #[verify::opaque]
    pub fn read(&self) -> ReadGuard<'_, T> {
        unimplemented!()
    }

    /// Acquire a write guard. EXPECTED: backward release `WriteGuard -> Result Unit`.
    #[verify::stateful_lifetimes]
    #[verify::opaque]
    pub fn write(&self) -> WriteGuard<'_, T> {
        unimplemented!()
    }

    /// Fallible acquire. EXPECTED: same release shape, wrapped in `Option`.
    #[verify::stateful_lifetimes]
    #[verify::opaque]
    pub fn try_read(&self) -> Option<ReadGuard<'_, T>> {
        unimplemented!()
    }

    /// Fallible acquire. EXPECTED: same release shape, wrapped in `Option`.
    #[verify::stateful_lifetimes]
    #[verify::opaque]
    pub fn try_write(&self) -> Option<WriteGuard<'_, T>> {
        unimplemented!()
    }

    /// Ordinary mutable borrow that bypasses the guard/release protocol
    /// entirely. EXPECTED: plain backward function, unaffected by this
    /// feature (no-regression case).
    #[verify::opaque]
    pub fn get_mut(&mut self) -> &mut T {
        unimplemented!()
    }

    /// The `&mut self` acquire counterpart to `write`: acquires a write
    /// guard via an *exclusive* borrow of the `Lock` handle itself, rather
    /// than a shared borrow. This models a lock variant whose fast-path
    /// acquire needs unique access to the handle (no atomics/interior
    /// mutability required). The receiver and returned guard share one
    /// region, so there is one fused backward:
    /// `WriteGuard T -> Lock T` today; the future stateful application is
    /// effectful. Returning the guard gives the
    /// receiver's state back; this is not two independent regions.
    #[verify::stateful_lifetimes]
    #[verify::opaque]
    pub fn acquire_exclusive(&mut self) -> WriteGuard<'_, T> {
        unimplemented!()
    }

    /// Two-region counterpart of `acquire_exclusive`: `'a` ties the guard
    /// to the lock, while `'b` is an independent ordinary mutable borrow.
    /// EXPECTED: one component per region. `'a` contributes the
    /// `WriteGuard -> Lock` backward; `'b` ends eagerly and contributes the
    /// returned counter value.
    #[verify::stateful_lifetimes('a)]
    #[verify::opaque]
    pub fn acquire_exclusive_counting<'a, 'b>(
        &'a mut self,
        _counter: &'b mut u32,
    ) -> WriteGuard<'a, T> {
        unimplemented!()
    }
}

impl<'a, T> ReadGuard<'a, T> {
    /// Shared deref through a read guard. EXPECTED: no backward function.
    #[verify::opaque]
    pub fn get(&self) -> &T {
        unimplemented!()
    }

    /// Explicit release, standing in for a guard's `Drop`. EXPECTED: this is
    /// exactly the `Guard -> Result Unit` backward function the feature
    /// should synthesize automatically once implemented.
    #[verify::stateful_lifetimes]
    #[verify::opaque]
    pub fn release(self) {}
}

impl<'a, T> WriteGuard<'a, T> {
    /// Shared deref through a write guard. EXPECTED: no backward function.
    #[verify::opaque]
    pub fn get(&self) -> &T {
        unimplemented!()
    }

    /// Mutable deref through a write guard. EXPECTED: one setter backward
    /// `T -> Result Guard` for the short method borrow and one outer-region
    /// backward `Guard -> Result Guard`. They are separate region
    /// components, not two releases.
    #[verify::stateful_lifetimes]
    #[verify::opaque]
    pub fn get_mut(&mut self) -> &mut T {
        unimplemented!()
    }

    /// Explicit release. EXPECTED: `Guard -> Result Unit` backward function.
    #[verify::stateful_lifetimes]
    #[verify::opaque]
    pub fn release(self) {}

    /// Downgrade a write guard into a read guard: consumes the write
    /// guard's own release obligation and produces a *different* guard
    /// value (a `ReadGuard`) with its own, independent release obligation.
    /// EXPECTED (future, currently unsupported): once stateful lifetimes
    /// lands, this "obligation replacement" pattern -- one guard's
    /// bookkeeping being consumed and substituted by a different guard's
    /// bookkeeping -- is expected to need dedicated support and may
    /// initially be rejected, or conservatively fall back to plain
    /// opaque-call translation, rather than being fully modeled. See
    /// `write_guard_downgrade_to_read` below.
    #[verify::stateful_lifetimes]
    #[verify::opaque]
    pub fn downgrade(self) -> ReadGuard<'a, T> {
        unimplemented!()
    }
}

/// Minimal write acquire/release: the smallest possible stateful shape.
#[verify::stateful_lifetimes]
pub fn minimal_write_acquire_release<T>(lock: &Lock<T>) {
    let guard = lock.write();
    guard.release();
}

/// Bare-vs-named equivalence: for a signature with exactly one lifetime
/// parameter, the *named* form below is DEFINED to mean exactly the same
/// thing as the *bare* form used by `minimal_write_acquire_release` above
/// -- naming the lock's borrow explicitly changes nothing about which
/// lifetime is stateful, since there is only one lifetime to name.
/// EXPECTED: both functions must translate identically once the feature
/// lands.
#[verify::stateful_lifetimes('a)]
pub fn minimal_write_acquire_release_named<'a, T>(lock: &'a Lock<T>) {
    let guard = lock.write();
    guard.release();
}

/// Named-list syntax permits a trailing comma and is semantically
/// identical to the one-element named form above.
#[verify::stateful_lifetimes('a,)]
pub fn minimal_write_acquire_release_trailing_comma<'a, T>(lock: &'a Lock<T>) {
    let guard = lock.write();
    guard.release();
}

/// Control case: identical body to `minimal_write_acquire_release`, but
/// with NO `#[verify::stateful_lifetimes]` attribute at all (the third,
/// distinct case from the bare/named forms -- see the module docs above).
/// EXPECTED: today, and after the feature lands, this function is
/// translated exactly like any ordinary opaque-call sequence -- guard/
/// release reasoning only ever applies to functions explicitly marked
/// with the attribute, in either its bare or named form.
pub fn unannotated_write_acquire_release<T>(lock: &Lock<T>) {
    let guard = lock.write();
    guard.release();
}

/// Minimal read acquire/release.
#[verify::stateful_lifetimes]
pub fn minimal_read_acquire_release<T>(lock: &Lock<T>) {
    let guard = lock.read();
    guard.release();
}

/// Fallible write acquire ("try-write" shape): the `Some` branch must still
/// produce the guard/release pair; the `None` branch has nothing to release.
#[verify::stateful_lifetimes]
pub fn try_write_acquire_release<T>(lock: &Lock<T>) -> bool {
    match lock.try_write() {
        Some(guard) => {
            guard.release();
            true
        }
        None => false,
    }
}

/// Fallible read acquire ("try-read" shape), mirroring `try_write_acquire_release`.
#[verify::stateful_lifetimes]
pub fn try_read_acquire_release<T>(lock: &Lock<T>) -> bool {
    match lock.try_read() {
        Some(guard) => {
            guard.release();
            true
        }
        None => false,
    }
}

/// Try-lock where the `Option<Guard>` is held in a local binding across
/// unrelated code before being matched, as opposed to `try_write_acquire_release`
/// above, which matches immediately. EXPECTED: the stateful reasoning must
/// track the guard through the `Option` regardless of how long it is held
/// before the match; delaying the match changes nothing about the
/// acquire/release pairing.
#[verify::stateful_lifetimes]
pub fn try_write_option_held_before_match<T>(lock: &Lock<T>, unrelated: i32) -> i32 {
    let maybe_guard = lock.try_write();
    let doubled = unrelated * 2;
    match maybe_guard {
        Some(guard) => {
            guard.release();
            doubled
        }
        None => doubled,
    }
}

/// Shared deref of a read guard, copying the value out. EXPECTED: no
/// backward function for the `get()` call itself, only the release.
#[verify::stateful_lifetimes]
pub fn read_guard_deref_copy(lock: &Lock<i32>) -> i32 {
    let guard = lock.read();
    let value = *guard.get();
    guard.release();
    value
}

/// Shared deref of a *write* guard (via `get`, not `get_mut`). EXPECTED: no
/// backward function, exactly like the read-guard case.
#[verify::stateful_lifetimes]
pub fn write_guard_deref_shared_copy(lock: &Lock<i32>) -> i32 {
    let guard = lock.write();
    let value = *guard.get();
    guard.release();
    value
}

/// Mutable deref of a write guard, single assignment. EXPECTED: exactly one
/// setter backward function `T -> Result Guard`.
#[verify::stateful_lifetimes('a)]
pub fn write_guard_deref_mut_set<'a>(lock: &'a Lock<i32>) {
    let mut guard = lock.write();
    *guard.get_mut() = 42;
    guard.release();
}

/// Mutable deref of a write guard, called repeatedly on the *same* guard.
/// EXPECTED: each call contributes its own setter/outer-region pair, and
/// the three pairs are sequenced through the updated guard. They must not
/// be merged into one global setter for the guard value.
#[verify::stateful_lifetimes]
pub fn write_guard_deref_mut_repeated(lock: &Lock<i32>) {
    let mut guard = lock.write();
    *guard.get_mut() = 1;
    *guard.get_mut() = 2;
    *guard.get_mut() += 3;
    guard.release();
}

/// `get_mut()` is called but its result is immediately discarded as a bare
/// statement (not assigned, not written through). EXPECTED: `get_mut()`
/// still creates the mutable-reborrow obligation -- Aeneas generates
/// backward functions based on the *type* of the call, not on whether the
/// caller later uses the returned reference -- so this still produces the
/// call's setter and outer-region components. Since nothing is written,
/// the setter receives the unchanged value.
#[verify::stateful_lifetimes]
pub fn write_guard_get_mut_unused<T>(lock: &Lock<T>) {
    let mut guard = lock.write();
    guard.get_mut();
    guard.release();
}

/// Interleaved shared and mutable deref of the same write guard: `get()`,
/// then `get_mut()`, then `get()` again. EXPECTED: the two shared derefs
/// contribute no backward function; the single `get_mut()` call still
/// contributes one setter and one outer-region backward, and interleaving
/// shared reads around it changes neither component.
#[verify::stateful_lifetimes]
pub fn write_guard_interleaved_shared_and_mut(lock: &Lock<i32>) -> i32 {
    let mut guard = lock.write();
    let before = *guard.get();
    *guard.get_mut() = 1;
    let after = *guard.get();
    guard.release();
    after
}

/// Guard downgrade: consumes a write guard's release obligation and
/// produces a read guard with its own, independent one. EXPECTED (future,
/// currently unsupported -- see `WriteGuard::downgrade` above): this
/// fixture is included so that, if/when downgrade support is added to the
/// stateful lifetimes feature, it is ready to serve as a regression test;
/// the initial implementation of the feature is not required to handle
/// this pattern precisely.
#[verify::stateful_lifetimes]
pub fn write_guard_downgrade_to_read<T>(lock: &Lock<T>) {
    let guard = lock.write();
    let read_guard = guard.downgrade();
    read_guard.release();
}

/// Generic `T` write guard shape (no `Copy`/`Default` bound needed since we
/// just overwrite the whole value).
#[verify::stateful_lifetimes]
pub fn generic_write_replace<T>(lock: &Lock<T>, value: T) {
    let mut guard = lock.write();
    *guard.get_mut() = value;
    guard.release();
}

/// Two independent locks, two independent stateful lifetimes. EXPECTED: two
/// independent release backward functions, one per guard.
#[verify::stateful_lifetimes('a, 'b)]
pub fn read_two_locks<'a, 'b, T: Copy, U: Copy>(lock1: &'a Lock<T>, lock2: &'b Lock<U>) -> (T, U) {
    let g1 = lock1.read();
    let g2 = lock2.read();
    let v1 = *g1.get();
    let v2 = *g2.get();
    g1.release();
    g2.release();
    (v1, v2)
}

/// Bare form with two lifetimes: by definition it marks both, in
/// declaration order, and is equivalent to `read_two_locks`'s named list.
#[verify::stateful_lifetimes]
pub fn read_two_locks_bare<'a, 'b, T: Copy, U: Copy>(
    lock1: &'a Lock<T>,
    lock2: &'b Lock<U>,
) -> (T, U) {
    let g1 = lock1.read();
    let g2 = lock2.read();
    let v1 = *g1.get();
    let v2 = *g2.get();
    g1.release();
    g2.release();
    (v1, v2)
}

/// Opaque method whose selected lifetime comes from the surrounding impl
/// binder rather than the method's own generic binder list.
#[verify::opaque]
pub struct ImplLifetimeLock<'a, T> {
    _marker: PhantomData<&'a Lock<T>>,
}

impl<'a, T> ImplLifetimeLock<'a, T> {
    #[verify::stateful_lifetimes('a)]
    #[verify::opaque]
    pub fn read_bound(&self) -> ReadGuard<'a, T> {
        unimplemented!()
    }
}

/// Mixed stateful and pure lifetimes in one signature: `'a` is stateful
/// (guards the lock), `'b` is an ordinary pure shared borrow. EXPECTED: `'a`
/// gets the guard/release treatment, `'b` is translated exactly as today
/// (plain, no backward function since it is a shared borrow).
#[verify::stateful_lifetimes('a)]
pub fn mixed_stateful_and_pure<'a, 'b, T: Copy>(lock: &'a Lock<T>, plain: &'b T) -> (T, T) {
    let guard = lock.read();
    let from_lock = *guard.get();
    let from_plain = *plain;
    guard.release();
    (from_lock, from_plain)
}

/// `get_mut` bypasses the lock/guard/release protocol entirely and returns a
/// plain `&mut T`. No-regression fixture: this function never acquires a
/// guard, so it carries NO `#[verify::stateful_lifetimes]` attribute (per
/// the "third case" defined in the module docs above) and keeps today's
/// ordinary backward-function translation, entirely unaffected by stateful
/// lifetimes.
pub fn get_mut_without_lock<T>(lock: &mut Lock<T>) -> &mut T {
    lock.get_mut()
}

/// Acquire via `&mut self` instead of `&self` (see `Lock::acquire_exclusive`
/// above): exercises the fused backward for the one region shared by the
/// `&mut Lock` receiver and returned guard.
#[verify::stateful_lifetimes]
pub fn write_guard_via_mut_self_acquire<T>(lock: &mut Lock<T>) {
    let guard = lock.acquire_exclusive();
    guard.release();
}

/// The genuine two-region composition case: `'a` is the lock/guard
/// lifetime and is marked stateful; `'b` is an ordinary mutable counter
/// lifetime. Their two region components must remain independent: one
/// backward function and one eager returned value.
#[verify::stateful_lifetimes('a)]
pub fn write_guard_via_mut_self_with_counter<'a, 'b, T>(
    lock: &'a mut Lock<T>,
    counter: &'b mut u32,
) {
    let guard = lock.acquire_exclusive_counting(counter);
    guard.release();
}

/// Acquiring a write guard but never calling `get`/`get_mut`, only
/// releasing it right away. EXPECTED: still exactly one release backward
/// function, with no setter (since `get_mut` was never called).
#[verify::stateful_lifetimes]
pub fn write_guard_release_only<T>(lock: &Lock<T>) {
    let guard = lock.write();
    guard.release();
}

/// Demonstrates that `ReadGuard<'a, T>` is *covariant* in `'a`: given
/// `'long: 'short`, a `ReadGuard<'long, T>` can be used directly as a
/// `ReadGuard<'short, T>` with no explicit reborrow, because
/// `ReadGuard`'s `PhantomData<&'a T>` field is covariant. EXPECTED: this
/// ordinary Rust subtyping is resolved before the stateful guard/release
/// treatment is applied, exactly as for any other covariant borrow; see
/// `outlives_chain` in `lt-stateful-reborrows.rs` for a stateful fixture
/// that relies on this same covariance.
pub fn read_guard_covariance<'long, 'short, T>(guard: ReadGuard<'long, T>) -> ReadGuard<'short, T>
where
    'long: 'short,
{
    guard
}

/// Contrast: `WriteGuard<'a, T>` is *invariant* in `'a` (its
/// `PhantomData<&'a mut T>` field is invariant), so the analogous
/// subtyping coercion used by `read_guard_covariance` above does **not**
/// type-check for `WriteGuard`, and is intentionally omitted here as
/// compiled code (it would fail to borrow-check, violating the
/// "valid Rust only" rule for this file). EXPECTED: once implemented, the
/// stateful lifetimes pass must respect this variance distinction -- it
/// must not assume `WriteGuard` is covariant merely because `ReadGuard` is,
/// and must not weaken a `WriteGuard`'s lifetime the way it may weaken a
/// `ReadGuard`'s.
///
/// The following, if uncommented, would NOT compile:
/// ```text
/// fn write_guard_would_not_be_covariant<'long, 'short, T>(
///     guard: WriteGuard<'long, T>,
/// ) -> WriteGuard<'short, T>
/// where
///     'long: 'short,
/// {
///     guard // error[E0308]: mismatched types (WriteGuard is invariant)
/// }
/// ```
#[verify::stateful_lifetimes]
pub fn write_guard_invariance_contrast<T>(lock: &Lock<T>) {
    let guard = lock.write();
    guard.release();
}
