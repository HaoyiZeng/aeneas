//@ [!lean] skip
//@ [lean] subdir=BackendFailures
#![feature(register_tool)]
#![register_tool(verify)]

//! # Stateful concurrency — Lean-backend failure
//!
//! Charon and Aeneas successfully generate
//! `tests/lean/BackendFailures/LtStatefulConcurrencyBackendFailures.lean`,
//! but Lean rejects it. The
//! closure's `FnOnce.call_once` definition returns both the worker result
//! and the mutable-capture backward state, while the synthesized `FnOnce`
//! trait instance expects only the worker result. The outer `spawn` call
//! similarly expects a plain `JoinHandle` instead of
//! `(JoinHandle × capture-state)`.
//!
//! The subdirectory keeps it outside the top-level lakefile generator.
//! Once closure trait types preserve mutable-capture backwards, remove the
//! subdir directive and move the fixture into `lt-stateful-concurrency.rs`.

use std::marker::PhantomData;

#[verify::opaque]
pub struct JoinHandle<T> {
    _marker: PhantomData<T>,
}

impl<T> JoinHandle<T> {
    #[verify::opaque]
    pub fn join(self) -> T {
        unimplemented!()
    }
}

#[verify::opaque]
pub fn spawn<F, T>(_f: F) -> JoinHandle<T>
where
    F: FnOnce() -> T,
{
    unimplemented!()
}

/// Future EXPECTED: the mutable borrow remains owned by the worker until
/// `join`; it must not be returned at the `spawn` call.
#[verify::stateful_lifetimes]
pub fn spawn_capturing_mut_borrow(x: &mut i32) -> i32 {
    let handle = spawn(|| {
        *x += 1;
        *x
    });
    handle.join()
}
