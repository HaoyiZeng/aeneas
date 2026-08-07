//@ [!lean] skip
//@ [lean] known-failure
#![feature(register_tool)]
#![register_tool(verify)]

//! Mutable subborrows projected through guard wrappers.
//! CURRENT: symbolic values are lost in `SymbolicToPureCore.ml`, line 520.

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
    pub fn write(&self) -> WriteGuard<'_, T> {
        unimplemented!()
    }
}

impl<'a, T> WriteGuard<'a, T> {
    #[verify::opaque]
    pub fn get_mut(&mut self) -> &mut T {
        unimplemented!()
    }

    #[verify::opaque]
    pub fn release(self) {}
}

pub struct Pair {
    pub a: i32,
    pub b: i32,
}

pub fn head_mut<'a>(guard: &'a mut WriteGuard<'_, Pair>) -> &'a mut i32 {
    &mut guard.get_mut().a
}

#[verify::stateful_lifetimes]
pub fn acquire_then_project_via_helper(lock: &Lock<Pair>) {
    let mut guard = lock.write();
    *head_mut(&mut guard) += 1;
    guard.release();
}

pub struct GuardBox<'p, T> {
    pub guard: WriteGuard<'p, T>,
}

pub fn project_nested_guard<'c, 'p, T>(wrapper: &'c mut GuardBox<'p, T>) -> &'c mut T {
    wrapper.guard.get_mut()
}
