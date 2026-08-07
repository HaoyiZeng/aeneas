//@ [!lean] skip
//@ [lean] subdir=BackendFailures
#![allow(dead_code, unused_variables, unused_mut)]

//! # Stateful optimizer suite — Lean-backend failure
//!
//! This is deliberately not a `//@ known-failure` test: Charon and Aeneas
//! both succeed and generate
//! `tests/lean/BackendFailures/LtStatefulPassBackendFailures.lean`. The
//! failure occurs only when Lean elaborates the generated closure trait
//! instances, and the current test runner has no marker for that category.
//! The `subdir=BackendFailures` directive keeps it outside the top-level
//! lakefile generator.
//!
//! EXPECTED: a higher-ranked closure returning a mutable borrow should
//! implement `Fn`/`FnMut`/`FnOnce` with the backward continuation reflected
//! in each method's result.
//!
//! CURRENT: the generated method definitions include that continuation,
//! while the synthesized trait instance types erase it. Lean reports type
//! mismatches such as `Result (I32 × (I32 → I32))` where `Result I32` is
//! expected. Once those trait types agree, remove the subdir directive and
//! move these functions into `lt-stateful-passes.rs`.

fn constrain<F>(f: F) -> F
where
    F: for<'r> Fn(&'r mut i32) -> &'r mut i32,
{
    f
}

pub fn closure_backward_borrow_once(x: &mut i32) -> i32 {
    let identity_closure = constrain(|y: &mut i32| -> &mut i32 { y });
    let r = identity_closure(x);
    *r += 1;
    *x
}

pub fn closure_backward_borrow_twice(x: &mut i32) -> i32 {
    let identity_closure = constrain(|y: &mut i32| -> &mut i32 { y });
    let r1 = identity_closure(x);
    *r1 += 1;
    let r2 = identity_closure(x);
    *r2 += 1;
    *x
}
