//@ [!lean] skip
//@ [lean] known-failure
#![feature(register_tool)]
#![register_tool(verify)]

//! Known closure/borrow baseline failure isolated from
//! `lt-stateful-signatures.rs`.
//!
//! Carrying a write guard through `Option::map` should preserve the guard's
//! release obligation across the closure boundary. Aeneas currently fails
//! while ending the closure's non-endable borrow abstraction in
//! `InterpBorrows.end_abs_aux`, before Lean extraction.

use std::marker::PhantomData;

#[verify::opaque]
pub struct Lock<T> {
    _marker: PhantomData<T>,
}

#[verify::opaque]
pub struct WriteGuard<'a, T> {
    _marker: PhantomData<&'a mut T>,
}

impl<T> Lock<T> {
    #[verify::opaque]
    pub fn try_write(&self) -> Option<WriteGuard<'_, T>> {
        unimplemented!()
    }
}

impl<'a, T> WriteGuard<'a, T> {
    #[verify::opaque]
    pub fn release(self) {}
}

/// EXPECTED AFTER IMPLEMENTATION:
/// `Option::map` may transform an owned guard without losing its stateful
/// lifetime. The guard returned by the closure remains releasable exactly
/// once after the combinator returns.
#[verify::stateful_lifetimes]
pub fn try_write_option_map_release<T>(lock: &Lock<T>) -> bool {
    match lock.try_write().map(|guard| (guard, true)) {
        Some((guard, tagged)) => {
            guard.release();
            tagged
        }
        None => false,
    }
}
