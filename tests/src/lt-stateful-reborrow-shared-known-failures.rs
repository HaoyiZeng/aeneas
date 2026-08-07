//@ [!lean] skip
//@ [lean] known-failure
#![feature(register_tool)]
#![register_tool(verify)]

//! Checked arithmetic is embedded in the RHS of an assignment whose place
//! is produced by `get_mut`. The place call separates the checked operation
//! from its dynamic-overflow assertion, so Aeneas reaches the unsupported
//! checked-binop arm in `InterpExpressions.ml`, line 1153. This is not a
//! shared-reborrow limitation; the passing hoisted form lives in
//! `lt-stateful-reborrows.rs`.

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

pub struct Pair {
    pub a: i32,
    pub b: i32,
}

#[verify::stateful_lifetimes]
pub fn checked_add_in_get_mut_assignment(lock: &Lock<Pair>, input: i32) -> i32 {
    let mut guard = lock.write();
    guard.get_mut().b = input + 1;
    let result = guard.get().b;
    guard.release();
    result
}
