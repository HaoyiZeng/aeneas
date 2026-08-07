//@ [!lean] skip
//! EXPECTED AFTER IMPLEMENTATION:
//! This file complements `lt-stateful-signatures.rs` and `lt-stateful-
//! reborrows.rs` and focuses on *wrapper* shapes for the future "stateful
//! lifetimes" feature: functions/methods that don't call `Lock::read` /
//! `Lock::write` directly but instead delegate to them through another
//! layer -- inherent wrappers, generic wrappers, trait methods (required
//! and default, across two independent concrete implementors), trait
//! objects (dynamic dispatch), opaque helpers that operate on an
//! already-acquired guard, autoderef through one or two non-erased `Deref`
//! hops (`Arc` and `Arc<Cell<_>>`), closures (both `Fn` and repeatedly-invoked
//! `FnMut`), a helper that projects a mutable subborrow out of a guard,
//! nested wrapper structs (transparent and opaque), and type aliases.
//! Every function below is annotated exactly as it is expected to be
//! annotated once the feature is implemented, and each doc comment states
//! whether the shape should be **SUPPORTED** (translated with the
//! guard/release bookkeeping described in `lt-stateful-signatures.rs`) or
//! is expected to remain an open problem / **EVENTUALLY-DIAGNOSED** shape
//! that the first implementation of the feature will likely have to reject
//! (see e.g. autoderef through `Arc` and guard-capturing closures below).
//!
//! CURRENT BASELINE:
//! `#[verify::stateful_lifetimes]` / `#[verify::stateful_lifetimes('a)]` are
//! inert tool attributes today (registered via `#![register_tool(verify)]`
//! but not yet interpreted by Aeneas). `Lock`, `ReadGuard`, and `WriteGuard`
//! are `#[verify::opaque]`, so every method call on them -- direct or
//! wrapped -- is extracted as an opaque call under the existing
//! translation. This file typechecks today and is meant to be usable
//! (unmodified, or with minimal changes) as a regression fixture once the
//! feature lands.
//!
//! Several shapes below that are documented **SUPPORTED** or
//! **EVENTUALLY-DIAGNOSED** currently make Aeneas itself error out (or, in
//! one case, crash with an uncaught exception) independently of anything
//! `#[verify::stateful_lifetimes]` specific, and have therefore been split
//! into emitter-specific `lt-stateful-wrapper-*-known-failures.rs` files so
//! this file's remaining fixtures keep translating:
//! dynamic dispatch through a `dyn` receiver (`acquire_read_via_dyn`), a
//! closure that acquires-then-releases its own guard (`Fn` and `FnMut`
//! variants: `closure_guard_contained`, `closure_repeated_fnmut`), a
//! closure that captures an already-acquired guard by move
//! (`closure_captures_guard`, retained in
//! `lt-stateful-misc-known-failures.rs` because it fails in
//! `SymbolicToPureTypes.ml:813`), a helper reborrowing a mutable subfield out
//! of a `&mut WriteGuard` (`head_mut` / `acquire_then_project_via_helper`),
//! reborrowing a mutable subfield out of an already-nested guard
//! (`project_nested_guard`), and constructing an opaque wrapper struct
//! around an already-acquired guard (`OpaqueGuardBox` / `wrap_guard_opaque`).
//! See those files' module docs for the precise errors.
#![feature(register_tool)]
#![register_tool(verify)]

use std::marker::PhantomData;
use std::ops::Deref;
use std::sync::Arc;

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

    #[verify::opaque]
    pub fn read(&self) -> ReadGuard<'_, T> {
        unimplemented!()
    }

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

    #[verify::opaque]
    pub fn release(self) {}
}

impl<'a, T> WriteGuard<'a, T> {
    #[verify::opaque]
    pub fn get(&self) -> &T {
        unimplemented!()
    }

    #[verify::opaque]
    pub fn get_mut(&mut self) -> &mut T {
        unimplemented!()
    }

    #[verify::opaque]
    pub fn release(self) {}
}

/// A plain (non-opaque) struct retained as wrapper payload vocabulary.
pub struct Pair {
    pub a: i32,
    pub b: i32,
}

// ---------------------------------------------------------------------
// 1. Inherent wrapper functions returning guards (elided vs named lifetime)
// ---------------------------------------------------------------------

/// A struct wrapping a `Lock<T>` one level deep.
pub struct Cache<T> {
    inner: Lock<T>,
}

impl<T> Cache<T> {
    #[verify::opaque]
    pub fn new(value: T) -> Self {
        Cache {
            inner: Lock::new(value),
        }
    }

    /// Inherent wrapper returning a guard, elided lifetime. EXPECTED:
    /// SUPPORTED -- a straightforward one-level delegation to
    /// `Lock::write`; the wrapper's own (elided) lifetime is exactly the
    /// lock's lifetime, same shape as `Lock::write` itself.
    #[verify::stateful_lifetimes]
    pub fn acquire_write(&self) -> WriteGuard<'_, T> {
        self.inner.write()
    }

    /// The same wrapper, but with the lifetime spelled out explicitly.
    /// EXPECTED: SUPPORTED -- identical translation to `acquire_write`
    /// above; naming the lifetime must not change the result.
    #[verify::stateful_lifetimes('a)]
    pub fn acquire_write_named<'a>(&'a self) -> WriteGuard<'a, T> {
        self.inner.write()
    }
}

// ---------------------------------------------------------------------
// 2. Generic wrappers (free functions)
// ---------------------------------------------------------------------

/// Generic free-function wrapper, elided lifetime. EXPECTED: SUPPORTED --
/// purely generic over `T`, no additional complications beyond the base
/// case in `lt-stateful-signatures.rs`.
#[verify::stateful_lifetimes]
pub fn acquire_generic<T>(lock: &Lock<T>) -> WriteGuard<'_, T> {
    lock.write()
}

/// Generic free-function wrapper with a trait bound and a named lifetime.
/// EXPECTED: SUPPORTED -- the `Default` bound doesn't interact with
/// lifetime/guard bookkeeping at all.
#[verify::stateful_lifetimes('a)]
pub fn acquire_generic_bound<'a, T: Default>(lock: &'a Lock<T>) -> WriteGuard<'a, T> {
    lock.write()
}

/// Generic wrapper combining two independent locks (mirrors
/// `read_two_locks` in `lt-stateful-signatures.rs`, but reached through the
/// `Cache`/`ReadLockable` wrapper layer). EXPECTED: SUPPORTED -- two
/// independent release backward functions, exactly as for the un-wrapped
/// two-lock case.
#[verify::stateful_lifetimes('a, 'b)]
pub fn acquire_two_via_wrappers<'a, 'b, T: Copy, U: Copy>(
    cache1: &'a Cache<T>,
    cache2: &'b Cache<U>,
) -> (T, U) {
    let g1 = cache1.acquire_read();
    let g2 = cache2.acquire_read();
    let v1 = *g1.get();
    let v2 = *g2.get();
    g1.release();
    g2.release();
    (v1, v2)
}

// ---------------------------------------------------------------------
// 3. Trait methods: required and default
// ---------------------------------------------------------------------

/// A trait exposing a required (non-default) guard-returning method.
pub trait ReadLockable {
    type Item;

    /// EXPECTED: SUPPORTED -- required trait method; the attribute is
    /// repeated identically on every concrete implementation (mirroring
    /// how ordinary preconditions/postconditions are repeated for trait
    /// methods elsewhere in Aeneas).
    #[verify::stateful_lifetimes]
    fn acquire_read(&self) -> ReadGuard<'_, Self::Item>;
}

impl<T> ReadLockable for Cache<T> {
    type Item = T;

    #[verify::stateful_lifetimes]
    fn acquire_read(&self) -> ReadGuard<'_, T> {
        self.inner.read()
    }
}

/// A trait with a default method that itself wraps `Lock::write`.
pub trait Lockable {
    type Item;

    fn lock_ref(&self) -> &Lock<Self::Item>;

    /// EXPECTED: SUPPORTED -- default trait method; every concrete `Self`
    /// shares this exact translation (no per-impl override needed).
    #[verify::stateful_lifetimes]
    fn acquire_write_default(&self) -> WriteGuard<'_, Self::Item> {
        self.lock_ref().write()
    }
}

impl<T> Lockable for Cache<T> {
    type Item = T;

    /// Plain (non-stateful) trait impl method: just an accessor, no guard
    /// is acquired here. EXPECTED: no annotation needed -- unaffected by
    /// the feature, exactly like `Lock::new` returning `Self`.
    fn lock_ref(&self) -> &Lock<T> {
        &self.inner
    }
}

/// A second, independent lock-wrapping struct, distinct from `Cache`. Its
/// only purpose is to give `ReadLockable` *two* concrete implementors
/// below, rather than one: the doc comment on `ReadLockable::acquire_read`
/// claims the attribute is "repeated identically on every concrete
/// implementation", a claim that is vacuous with a single implementor.
pub struct Vault<T> {
    guarded: Lock<T>,
}

impl<T> ReadLockable for Vault<T> {
    type Item = T;

    /// EXPECTED: SUPPORTED -- identical shape and identical annotation to
    /// `Cache`'s own `acquire_read` impl above, on an unrelated concrete
    /// type; this is the second implementor that makes the "repeated
    /// identically on every concrete implementation" claim non-vacuous.
    #[verify::stateful_lifetimes]
    fn acquire_read(&self) -> ReadGuard<'_, T> {
        self.guarded.read()
    }
}

// ---------------------------------------------------------------------
// 3a. Clients that actually invoke the wrapper surfaces
// ---------------------------------------------------------------------

#[verify::stateful_lifetimes]
pub fn via_inherent_wrapper_then_release(cache: &Cache<i32>) -> i32 {
    let guard = cache.acquire_write();
    let value = *guard.get();
    guard.release();
    value
}

#[verify::stateful_lifetimes]
pub fn via_trait_method_then_release(cache: &Cache<i32>) -> i32 {
    let guard = ReadLockable::acquire_read(cache);
    let value = *guard.get();
    guard.release();
    value
}

#[verify::stateful_lifetimes]
pub fn via_default_trait_method_then_release(cache: &Cache<i32>) {
    let mut guard = Lockable::acquire_write_default(cache);
    *guard.get_mut() = 7;
    guard.release();
}

#[verify::stateful_lifetimes]
pub fn via_generic_trait_bound<L: ReadLockable<Item = i32>>(lockable: &L) -> i32 {
    let guard = lockable.acquire_read();
    let value = *guard.get();
    guard.release();
    value
}

// ---------------------------------------------------------------------
// 3b. Trait objects (dynamic dispatch)
//
// `acquire_read_via_dyn` (calling `ReadLockable::acquire_read` through a
// `&dyn ReadLockable<Item = T>` trait object) has been moved to
// `lt-stateful-wrapper-dyn-known-failures.rs`:
// Aeneas does not support function pointers / dynamic dispatch through
// `dyn` receivers yet, so this shape currently errors out rather than
// merely being a documented open problem.
// ---------------------------------------------------------------------

// ---------------------------------------------------------------------
// 4. Opaque function taking `&mut Guard`
// ---------------------------------------------------------------------

/// A free function taking a live guard by exclusive reference (not as a
/// method receiver): it doesn't itself acquire or release anything, it
/// only pokes at an already-held guard.
#[verify::opaque]
pub fn poke_guard<T>(_guard: &mut WriteGuard<'_, T>) {
    unimplemented!()
}

/// Caller exercising `poke_guard` alongside the ordinary acquire/release
/// pattern. EXPECTED: SUPPORTED -- from the guard/release feature's point
/// of view, `poke_guard` is just another opaque call site that borrows the
/// guard mutably without consuming it; the caller's own guard still gets
/// exactly one release.
#[verify::stateful_lifetimes]
pub fn acquire_then_poke<T>(lock: &Lock<T>) {
    let mut guard = lock.write();
    poke_guard(&mut guard);
    guard.release();
}

// ---------------------------------------------------------------------
// 5. Autoderef through `Arc<Lock<T>>`
// ---------------------------------------------------------------------

/// Autoderef through `Arc<Lock<T>>`: `.write()` resolves through `Deref`
/// from `&Arc<Lock<T>>` to `&Lock<T>` before landing on the opaque method.
/// EXPECTED: EVENTUALLY-DIAGNOSED (open problem) -- the stateful lifetime
/// here is threaded through an extra `Deref` hop that neither
/// `lt-stateful-signatures.rs` nor `lt-stateful-reborrows.rs` exercise;
/// whether the feature can see through autoderef method resolution to find
/// the borrow of the `Lock` (as opposed to the `Arc` itself) is an open
/// question for the first implementation, which may simply reject this
/// shape until autoderef support is added.
#[verify::stateful_lifetimes('a)]
pub fn acquire_via_arc<'a, T>(lock: &'a Arc<Lock<T>>) -> WriteGuard<'a, T> {
    lock.write()
}

/// Read-guard variant of the autoderef case above. EXPECTED:
/// EVENTUALLY-DIAGNOSED for the same reason as `acquire_via_arc`.
#[verify::stateful_lifetimes]
pub fn acquire_via_arc_read<T>(lock: &Arc<Lock<T>>) -> ReadGuard<'_, T> {
    lock.read()
}

/// A user-defined wrapper retained by Aeneas (unlike `Box`, which is
/// erased), used to make a genuine second `Deref` hop visible.
pub struct Cell<T> {
    inner: T,
}

impl<T> Deref for Cell<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

/// Two-hop autoderef: `Arc<Cell<Lock<T>>>`. `.write()` resolves through
/// *two* visible `Deref` hops (`&Arc<Cell<Lock<T>>>` -> `&Cell<Lock<T>>` ->
/// `&Lock<T>`) before landing on the opaque method, one hop deeper than
/// `acquire_via_arc` above. EXPECTED: EVENTUALLY-DIAGNOSED for the same
/// reason as the single-hop case, compounded: whatever mechanism the first
/// implementation might use to see through one autoderef hop (if any)
/// would need to be applied twice, not once, making this shape strictly
/// harder than `acquire_via_arc` rather than merely another instance of it.
#[verify::stateful_lifetimes]
pub fn acquire_via_arc_cell<T>(lock: &Arc<Cell<Lock<T>>>) -> WriteGuard<'_, T> {
    lock.write()
}

// ---------------------------------------------------------------------
// 6. Closures: guard fully contained vs guard captured (escaping)
//
// `closure_guard_contained` (a closure that acquires and releases its own
// guard entirely within its body) and `closure_repeated_fnmut` (a `FnMut`
// closure repeating the same acquire/release pattern once per call) have
// both been moved to `lt-stateful-wrapper-closure-known-failures.rs`:
// despite being documented as SUPPORTED, Aeneas today hits an
// internal error (`InterpProjectors.apply_proj_borrows_on_input_value`)
// while translating the synthesized `call`/`call_mut` operator for a
// closure whose body itself acquires-then-releases an opaque guard.
// ---------------------------------------------------------------------

// ---------------------------------------------------------------------
// 7. Helper returning a mutable subborrow out of a guard
//
// `head_mut` / `acquire_then_project_via_helper` (a plain, non-stateful
// helper that reborrows a mutable subfield out of an already-borrowed
// write guard, called from a caller that acquires/releases the guard
// itself) has been moved to
// `lt-stateful-wrapper-projection-known-failures.rs`: despite carrying no
// `#[verify::stateful_lifetimes]`
// attribute at all and being documented as SUPPORTED, Aeneas currently
// fails with `Could not find var for symbolic value` while translating
// `head_mut` itself.
// ---------------------------------------------------------------------

// ---------------------------------------------------------------------
// 8. Nested wrapper structs
// ---------------------------------------------------------------------

/// A struct nesting an already-acquired guard one level deep.
pub struct GuardBox<'p, T> {
    pub guard: WriteGuard<'p, T>,
}

/// Construct the wrapper around an already-acquired guard. EXPECTED:
/// SUPPORTED -- the wrapper's own lifetime parameter `'p` is *exactly* the
/// guard's lifetime, a one-to-one passthrough introducing no new region.
#[verify::stateful_lifetimes('p)]
pub fn wrap_guard<'p, T>(guard: WriteGuard<'p, T>) -> GuardBox<'p, T> {
    GuardBox { guard }
}

// Reborrow of a mutable subfield out of an already-nested guard is in
// `lt-stateful-wrapper-projection-known-failures.rs`. It is an ordinary
// pure reborrow with no stateful annotation, but Aeneas currently loses a
// symbolic value.

/// A second level of nesting: a wrapper around a wrapper around a guard.
pub struct DoubleGuardBox<'p, T> {
    pub inner: GuardBox<'p, T>,
}

/// EXPECTED: SUPPORTED -- same one-to-one passthrough reasoning as
/// `wrap_guard`, just applied twice; the region `'p` still names the one
/// and only acquired guard, regardless of how many wrapper layers sit atop
/// it.
#[verify::stateful_lifetimes('p)]
pub fn wrap_guard_twice<'p, T>(guard: WriteGuard<'p, T>) -> DoubleGuardBox<'p, T> {
    DoubleGuardBox {
        inner: GuardBox { guard },
    }
}

/// End-to-end client for the transparent wrapper: acquire, wrap, mutate
/// through the field, then release the same guard.
#[verify::stateful_lifetimes]
pub fn acquire_wrap_use_release(lock: &Lock<i32>) {
    let guard = lock.write();
    let mut boxed = wrap_guard(guard);
    *boxed.guard.get_mut() = 9;
    boxed.guard.release();
}

// The opaque nested-guard wrapper shape lives in
// `lt-stateful-wrapper-opaque-known-failures.rs`. Aeneas currently raises
// an uncaught `Invalid_argument` while processing the opaque fields.

// ---------------------------------------------------------------------
// 9. Type aliases
// ---------------------------------------------------------------------

/// A type alias for a concrete guard instantiation. EXPECTED: SUPPORTED --
/// the attribute checker must resolve through the alias to find the
/// underlying `WriteGuard<'a, i32>` before applying stateful-lifetime
/// reasoning, exactly like Aeneas already resolves ordinary type aliases
/// elsewhere in the pipeline.
pub type IntWriteGuard<'a> = WriteGuard<'a, i32>;

#[verify::stateful_lifetimes('a)]
pub fn acquire_via_alias<'a>(lock: &'a Lock<i32>) -> IntWriteGuard<'a> {
    lock.write()
}

/// A type alias over a nested wrapper struct (`GuardBox` from section 8).
/// EXPECTED: SUPPORTED for the same reason as `acquire_via_alias` -- alias
/// resolution is orthogonal to how many wrapper layers the aliased type
/// itself contains.
pub type IntGuardBox<'p> = GuardBox<'p, i32>;

#[verify::stateful_lifetimes('p)]
pub fn wrap_guard_via_alias<'p>(guard: WriteGuard<'p, i32>) -> IntGuardBox<'p> {
    IntGuardBox { guard }
}
