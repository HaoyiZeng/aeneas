//@ [!lean] skip
//@ [lean] known-failure
#![feature(register_tool)]
#![register_tool(verify)]

//! An opaque wrapper contains a guard field.
//! CURRENT: Aeneas raises an uncaught `Invalid_argument` while retrieving
//! fields of the opaque ADT. The failure is printed on stderr, so the
//! checked `.lean.out` may contain only the preceding import line.

use std::marker::PhantomData;

#[verify::opaque]
pub struct WriteGuard<'a, T> {
    _marker: PhantomData<&'a mut T>,
}

#[verify::opaque]
pub struct OpaqueGuardBox<'p, T> {
    pub guard: WriteGuard<'p, T>,
}

#[verify::stateful_lifetimes('p)]
pub fn wrap_guard_opaque<'p, T>(guard: WriteGuard<'p, T>) -> OpaqueGuardBox<'p, T> {
    OpaqueGuardBox { guard }
}
