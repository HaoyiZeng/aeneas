//@ [!lean] skip
//@ [lean] known-failure
#![feature(register_tool)]
#![register_tool(verify)]

//! Known concurrency/borrow failure: a spawned closure returns a guard and
//! the parent receives it at `join`. Aeneas currently fails while ending
//! the closure's non-endable abstraction (`InterpBorrows.ml`, line 1203).
//! This is the concurrent counterpart of
//! `lt-stateful-signature-closure-known-failures.rs`.

use std::marker::PhantomData;

#[verify::opaque]
pub struct JoinHandle<T> {
    _marker: PhantomData<T>,
}

impl<T> JoinHandle<T> {
    #[verify::opaque]
    pub fn join(self) -> T {
        unimplemented!()
    }
}

#[verify::opaque]
pub fn spawn<F, T>(_f: F) -> JoinHandle<T>
where
    F: FnOnce() -> T,
{
    unimplemented!()
}

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
pub fn worker_returns_read_guard(lock: &Lock<i32>) -> i32 {
    let handle = spawn(|| lock.read());
    let guard = handle.join();
    let value = *guard.get();
    guard.release();
    value
}
