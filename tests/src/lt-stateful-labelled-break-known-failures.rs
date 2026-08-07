//@ [!lean] skip
//@ [lean] known-failure
//@ [lean] aeneas-args=-loops-to-rec
#![feature(register_tool)]
#![register_tool(verify)]

//! Labelled `break`/`continue` from an inner loop to an outer loop.
//! CURRENT: `PrePasses.ml`, line 648, "Breaks to outer loops are not
//! supported yet".

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

#[verify::stateful_lifetimes]
pub fn nested_loops_labelled_break_continue(
    lock: &Lock<i32>,
    outer_n: u32,
    inner_n: u32,
    stop_value: i32,
) -> i32 {
    let mut total = 0;
    'outer: for _ in 0..outer_n {
        for i in 0..inner_n {
            let guard = lock.read();
            let value = *guard.get();
            guard.release();
            if value == stop_value {
                break 'outer;
            }
            if i % 2 == 0 {
                continue 'outer;
            }
            total += value;
        }
    }
    total
}
