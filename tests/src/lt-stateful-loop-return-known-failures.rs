//@ [!lean] skip
//@ [lean] known-failure
//@ [lean] aeneas-args=-loops-to-rec
#![feature(register_tool)]
#![register_tool(verify)]

//! A loop exits with an open guard as its value.
//! CURRENT: loop context joining reaches `InterpJoin.ml`, line 1311.

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
    pub fn get(&self) -> &T {
        unimplemented!()
    }

    #[verify::opaque]
    pub fn release(self) {}
}

#[verify::stateful_lifetimes]
pub fn loop_returns_guard_as_break_value(lock: &Lock<i32>, threshold: i32) -> i32 {
    let guard = loop {
        let guard = lock.write();
        if *guard.get() > threshold {
            break guard;
        }
        guard.release();
    };
    let value = *guard.get();
    guard.release();
    value
}

#[verify::stateful_lifetimes]
pub fn loop_break_value_is_function_return(
    lock: &Lock<i32>,
    threshold: i32,
) -> WriteGuard<'_, i32> {
    loop {
        let guard = lock.write();
        if *guard.get() > threshold {
            break guard;
        }
        guard.release();
    }
}
