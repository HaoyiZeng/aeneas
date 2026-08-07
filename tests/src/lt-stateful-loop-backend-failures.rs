//@ [!lean] skip
//@ [lean] subdir=BackendFailures
#![feature(register_tool)]
#![register_tool(verify)]

//! # Stateful loops — Lean-backend failure
//!
//! Aeneas generates this iterator-combinator fixture successfully, but the
//! generated Lean does not elaborate: the modeled iterator trait lacks the
//! generated `map`/`sum` field path. The subdirectory keeps the module
//! outside the top-level lakefile generator until that backend gap is fixed.

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

#[verify::stateful_lifetimes]
pub fn iterator_adapter_sum_with_guard(lock: &Lock<i32>, n: u32) -> i32 {
    (0..n)
        .map(|i| {
            let mut guard = lock.write();
            *guard.get_mut() += 1;
            let value = *guard.get();
            guard.release();
            value + i as i32
        })
        .sum()
}
