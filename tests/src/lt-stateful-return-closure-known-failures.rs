//@ [!lean] skip
//@ [lean] known-failure
#![feature(register_tool)]
#![register_tool(verify)]

//! A closure creates and returns a guard.
//! CURRENT: Aeneas cannot end the closure's non-endable abstraction
//! (`InterpBorrows.ml`, line 1203).

#[verify::opaque]
pub struct Lock;

#[verify::opaque]
pub struct Guard<'a> {
    lock: &'a Lock,
}

#[verify::opaque]
pub fn acquire(lock: &Lock) -> Guard<'_> {
    unimplemented!()
}

pub fn closure_returns_guard(lock: &Lock) -> Guard<'_> {
    let make = || acquire(lock);
    make()
}
