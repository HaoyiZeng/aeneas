//@ [!lean] skip
//@ [lean] known-failure
#![feature(register_tool)]
#![register_tool(verify)]

//! A helper calls `get_mut` through `&mut WriteGuard`.
//! CURRENT: even one projected store reaches an unreachable given-back value in
//! `SymbolicToPureValues.ml`, line 896.

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

fn set_pair_via_borrowed_guard(guard: &mut WriteGuard<'_, Pair>) {
    guard.get_mut().a = 1;
}

#[verify::stateful_lifetimes]
pub fn borrowed_guard_get_mut(lock: &Lock<Pair>) {
    let mut guard = lock.write();
    set_pair_via_borrowed_guard(&mut guard);
    guard.release();
}
