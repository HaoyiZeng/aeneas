//@ [!lean] skip
//@ [lean] known-failure
//@ [lean] aeneas-args=-loops-to-rec
#![feature(register_tool)]
#![register_tool(verify)]

//! A loop-carried guard conditionally changes lock identity.
//! CURRENT: context matching fails in `InterpMatchCtxs.ml`, line 1330.

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
    pub fn get_mut(&mut self) -> &mut T {
        unimplemented!()
    }

    #[verify::opaque]
    pub fn release(self) {}
}

#[verify::stateful_lifetimes('a)]
pub fn guard_conditionally_replaced_in_loop<'a>(
    lock_a: &'a Lock<i32>,
    lock_b: &'a Lock<i32>,
    n: u32,
    switch_at: u32,
) -> i32 {
    let mut guard = lock_a.write();
    let mut i = 0;
    let mut using_b = false;
    while i < n {
        if !using_b && i == switch_at {
            guard.release();
            guard = lock_b.write();
            using_b = true;
        }
        *guard.get_mut() += 1;
        i += 1;
    }
    let result = *guard.get();
    guard.release();
    result
}
