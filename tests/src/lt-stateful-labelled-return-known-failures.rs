//@ [!lean] skip
//@ [lean] known-failure
//@ [lean] aeneas-args=-loops-to-rec
#![feature(register_tool)]
#![register_tool(verify)]

//! A labelled break carrying a guard out of nested loops.
//! CURRENT: `PrePasses.ml`, line 658, "Returns inside of nested loops are
//! not supported yet".

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
pub fn labelled_break_carries_guard_out_of_nested_loop(
    lock: &Lock<i32>,
    outer_n: u32,
    threshold: i32,
) -> i32 {
    let guard = 'outer: loop {
        for _ in 0..outer_n {
            let guard = lock.write();
            if *guard.get() > threshold {
                break 'outer guard;
            }
            guard.release();
        }
    };
    let value = *guard.get();
    guard.release();
    value
}
