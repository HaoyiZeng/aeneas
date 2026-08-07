//@ [!lean] skip
//@ [lean] known-failure
#![feature(register_tool)]
#![register_tool(verify)]

//! Closures acquire and release guards entirely within each invocation.
//! CURRENT: synthesized closure calls reach `InterpProjectors.ml`, line
//! 544.

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
    pub fn release(self) {}
}

#[verify::stateful_lifetimes]
pub fn closure_guard_contained<T: Copy>(lock: &Lock<T>) -> impl Fn() -> T + '_ {
    move || {
        let guard = lock.read();
        let value = *guard.get();
        guard.release();
        value
    }
}

#[verify::stateful_lifetimes]
pub fn closure_repeated_fnmut<T: Copy>(lock: &Lock<T>) -> impl FnMut() -> T + '_ {
    let mut calls: u32 = 0;
    move || {
        calls += 1;
        debug_assert!(calls >= 1);
        let guard = lock.write();
        let value = *guard.get();
        guard.release();
        value
    }
}
