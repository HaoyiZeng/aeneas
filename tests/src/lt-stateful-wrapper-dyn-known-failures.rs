//@ [!lean] skip
//@ [lean] known-failure
#![feature(register_tool)]
#![register_tool(verify)]

//! Guard acquisition through a `dyn` trait receiver.
//! CURRENT: function-pointer dispatch is rejected in
//! `InterpStatements.ml`, line 1398.

use std::marker::PhantomData;

#[verify::opaque]
pub struct ReadGuard<'a, T> {
    _marker: PhantomData<&'a T>,
}

pub trait ReadLockable {
    type Item;

    #[verify::stateful_lifetimes]
    fn acquire_read(&self) -> ReadGuard<'_, Self::Item>;
}

#[verify::stateful_lifetimes]
pub fn acquire_read_via_dyn<T>(lockable: &dyn ReadLockable<Item = T>) -> ReadGuard<'_, T> {
    lockable.acquire_read()
}
