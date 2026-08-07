//@ [!lean] skip
//@ [lean] known-failure
#![feature(register_tool)]
#![register_tool(verify)]

//! Known baseline failure isolated from `lt-stateful-signatures.rs`.
//!
//! The `'a: 'static` constraint currently triggers an internal error in
//! `RegionsHierarchy.compute_regions_hierarchy_for_sig`. Keeping this fixture
//! separate lets the normal signature suite generate while preserving the
//! reproducer and its expected future stateful-lifetime behavior.

use std::marker::PhantomData;

#[verify::opaque]
pub struct Lock<T> {
    _marker: PhantomData<T>,
}

#[verify::opaque]
pub struct ReadGuard<'a, T> {
    _marker: PhantomData<&'a T>,
}

impl<T> Lock<T> {
    #[verify::opaque]
    pub fn read(&self) -> ReadGuard<'_, T> {
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

/// EXPECTED AFTER IMPLEMENTATION:
/// `read` returns a guard with one effectful release backward. The `'static`
/// outlives constraint must not crash region hierarchy construction.
#[verify::stateful_lifetimes('a)]
pub fn static_lock_read<'a, T: Copy>(lock: &'a Lock<T>) -> T
where
    'a: 'static,
{
    let guard = lock.read();
    let value = *guard.get();
    guard.release();
    value
}
