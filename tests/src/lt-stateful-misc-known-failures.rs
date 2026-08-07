//@ [!lean] skip
//@ [lean] known-failure
#![feature(register_tool)]
#![register_tool(verify)]

//! A closure captures an already-acquired write guard.
//! CURRENT: the closure environment contains an unexpected erased region
//! (`SymbolicToPureTypes.ml`, line 813).

use std::marker::PhantomData;

#[verify::opaque]
pub struct WriteGuard<'a, T> {
    _marker: PhantomData<&'a mut T>,
}

impl<'a, T> WriteGuard<'a, T> {
    #[verify::opaque]
    pub fn get(&self) -> &T {
        unimplemented!()
    }
}

#[verify::stateful_lifetimes('a)]
pub fn closure_captures_guard<'a, T: Copy>(guard: WriteGuard<'a, T>) -> impl Fn() -> T + 'a {
    move || *guard.get()
}
