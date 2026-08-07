//@ [!lean] skip
//@ [lean] known-failure
#![feature(register_tool)]
#![register_tool(verify)]

//! Known baseline failure isolated from `lt-stateful-concurrency.rs`.
//!
//! ## What this file is
//! The scoped-thread-shaped API -- `Scope<'scope, 'env>`, `Scope::spawn`,
//! and the `scope` free function, matching the *shape* of
//! `std::thread::scope`/`std::thread::Scope` -- together with the two
//! fixtures that exercise it (`scoped_spawn_shape`,
//! `scoped_spawn_no_explicit_join`). This is the smallest self-contained
//! prelude needed to reproduce the baseline failure below: only
//! `JoinHandle<T>` (returned by `Scope::spawn`) and the `Scope`/`scope`
//! shape itself are duplicated here; none of the other opaque types from
//! `lt-stateful-concurrency.rs` (`FallibleJoinHandle`, `Arc`, `Lock`,
//! `ReadGuard`, ...) are needed to trigger it.
//!
//! ## CURRENT BASELINE
//! The `scope` free function's signature requires a higher-ranked bound
//! over the *scoped* lifetime `'scope`:
//! ```ignore
//! pub fn scope<'env, F, R>(_f: F) -> R
//! where
//!     F: for<'scope> FnOnce(&'scope Scope<'scope, 'env>) -> R,
//! { ... }
//! ```
//! Because `Scope<'scope, 'env>` also mentions the *free* (non-higher-ranked)
//! lifetime `'env`, this `for<'scope> ...` bound relates the higher-ranked
//! `'scope` to the free `'env`. Aeneas's region-hierarchy construction does
//! not support this today and aborts with:
//! ```text
//! [Error] Unimplemented: found an occurrence of a lifetime constraint relating
//!          a higher-ranked lifetime to a free lifetime.
//! Source: 'tests/src/lt-stateful-concurrency.rs', lines 255:0-260:1
//! Compiler source: llbc/TypesAnalysis.ml, line 970
//! ```
//! (line numbers are from the original, undivided file; the same `scope`
//! definition is reproduced below). This crash currently aborts extraction
//! for the *entire* crate it's compiled as part of -- which is exactly why
//! `scoped_spawn_shape` and `scoped_spawn_no_explicit_join` (the only two
//! fixtures in `lt-stateful-concurrency.rs` that reference `Scope`/`scope`)
//! were moved here, into their own `known-failure` fixture: isolating them
//! lets the rest of that suite (ordinary, non-scoped spawn/join shapes)
//! keep generating successfully.
//!
//! ## EXPECTED AFTER IMPLEMENTATION
//! See the module doc and the `Scope` doc comment below for the full
//! concurrency-events rationale:
//! letting a worker borrow non-`'static` data from the enclosing scope
//! requires generalizing the stateful-lifetimes machinery from
//! `lt-stateful-signatures.rs` to a *concurrent* join point (the scope's
//! closing `}`) rather than the ordinary sequential drop point used
//! elsewhere. That generalization -- and, as a prerequisite, teaching
//! Aeneas's region-hierarchy construction to handle a higher-ranked
//! lifetime related to a free lifetime -- is future work beyond both the
//! Arc/Weak and the concurrency-events features taken individually.
//!
//! **If this ever stops failing** (i.e.
//! `make test-lt-stateful-concurrency-known-failures.rs` starts producing
//! a clean, non-error `.out` file), move `Scope`/`scope`,
//! `scoped_spawn_shape`, and `scoped_spawn_no_explicit_join` back into
//! `lt-stateful-concurrency.rs` (restoring the cross-references removed
//! from its module doc) and update this file's status accordingly.

use std::marker::PhantomData;

// ---------------------------------------------------------------------
// Opaque spawn / join prelude (minimal duplicate of the one in
// `lt-stateful-concurrency.rs` -- only `JoinHandle` is needed here, since
// `Scope::spawn` returns it; the free `spawn` function, `FallibleJoinHandle`,
// `Arc`, and `Lock` are not required to trigger the baseline failure)
// ---------------------------------------------------------------------

/// An opaque handle to a spawned worker, mirroring
/// `std::thread::JoinHandle<T>`.
#[verify::opaque]
pub struct JoinHandle<T> {
    _marker: PhantomData<T>,
}

impl<T> JoinHandle<T> {
    /// Block until the worker finishes and recover its result.
    #[verify::opaque]
    pub fn join(self) -> T {
        unimplemented!()
    }
}

// ---------------------------------------------------------------------
// Opaque scoped-spawn prelude -- this is the shape that currently crashes
// Aeneas's region-hierarchy construction (see the module doc above)
// ---------------------------------------------------------------------

/// An opaque scoped-spawn handle, matching the *shape* of
/// `std::thread::Scope<'scope, 'env>`.
#[verify::opaque]
pub struct Scope<'scope, 'env> {
    _marker: PhantomData<(&'scope (), &'env ())>,
}

impl<'scope, 'env> Scope<'scope, 'env> {
    #[verify::opaque]
    pub fn spawn<F, T>(&'scope self, _f: F) -> JoinHandle<T>
    where
        F: FnOnce() -> T + 'scope,
    {
        unimplemented!()
    }
}

/// An opaque `std::thread::scope`-shaped entry point. This signature's
/// `for<'scope> FnOnce(&'scope Scope<'scope, 'env>) -> R` bound is the
/// higher-ranked-lifetime-related-to-a-free-lifetime shape that Aeneas
/// currently rejects (see the module doc above).
#[verify::opaque]
pub fn scope<'env, F, R>(_f: F) -> R
where
    F: for<'scope> FnOnce(&'scope Scope<'scope, 'env>) -> R,
{
    unimplemented!()
}

// ---------------------------------------------------------------------
// Scoped-thread-shaped fixtures (documented future / known unsupported)
// ---------------------------------------------------------------------

/// Scoped-thread-shaped spawn: the worker borrows `data` rather than
/// owning it, exactly the pattern real `std::thread::scope` exists to
/// support. EXPECTED / KNOWN UNSUPPORTED: see the module doc above --
/// modeling this borrow correctly is future work beyond both the Arc/Weak
/// and the concurrency-events features taken individually.
#[verify::stateful_lifetimes]
pub fn scoped_spawn_shape(data: &i32) -> i32 {
    scope(|s| {
        let handle = s.spawn(|| *data);
        handle.join()
    })
}

/// A scoped worker whose `JoinHandle` is simply dropped, rather than
/// explicitly joined, before the scope's closing `}`. EXPECTED / KNOWN
/// UNSUPPORTED: unlike a plain, un-scoped `JoinHandle` (which never
/// auto-joins), real `std::thread::scope` still *implicitly* joins every
/// unjoined scoped handle at the scope's own closing brace -- see the
/// module doc above for why modeling this correctly is out of scope for
/// both features taken individually.
#[verify::stateful_lifetimes]
pub fn scoped_spawn_no_explicit_join(data: &i32) -> i32 {
    scope(|s| {
        let _handle = s.spawn(|| {
            let _ = *data;
        });
        *data
    })
}
