//@ [!lean] skip
//@ [lean] known-failure
//@ [lean] aeneas-args=-loops-to-rec
#![feature(register_tool)]
#![register_tool(verify)]

//! A loop stores guard-owning closures behind `dyn FnOnce`.
//! CURRENT: dynamic trait types are rejected in
//! `SymbolicToPureTypes.ml`, line 547.

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
pub fn unsupported_closure_escape_guard_capture(lock: &Lock<i32>, n: u32) -> i32 {
    let mut callbacks: Vec<Box<dyn FnOnce() -> i32 + '_>> = Vec::new();
    for _ in 0..n {
        let guard = lock.write();
        callbacks.push(Box::new(move || {
            let value = *guard.get();
            guard.release();
            value
        }));
    }
    callbacks.into_iter().map(|callback| callback()).sum()
}
