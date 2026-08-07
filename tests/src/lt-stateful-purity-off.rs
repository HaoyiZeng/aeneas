//@ [!lean] skip
//@ [lean] aeneas-args=-eval-drops
#![allow(dead_code, unused_variables, unused_mut)]

//! # The `-stateful-lifetimes` flag must be inert without annotations
//!
//! This crate contains **no** `#[verify::stateful_lifetimes]` annotation.  It
//! exists in two identical copies, `lt-stateful-purity-off.rs` and
//! `lt-stateful-purity-on.rs`, translated with and without the flag.
//! `tests/lean/LtStatefulPurityCheck.lean` asserts the two translations are
//! equal, function by function.
//!
//! This is a regression test for the flag being a *global mode switch* rather
//! than a per-lifetime property.  Two things currently make it global:
//!
//!   * `SymbolicToPureAbs.abs_to_ty` computes
//!     `!Config.stateful_lifetimes || abs_cont_is_monadic ctx abs`, so **every**
//!     loop and join continuation becomes `Result`-valued when the flag is on,
//!     even with nothing annotated;
//!   * `abs_cont_to_texpr_aux` unconditionally `ok`-wraps the continuation
//!     output for the same reason.
//!
//! Those over-approximations are what forced `remove_ignored_trivial_lets` and
//! the weakening of `simplify_let_bindings` into the pipeline.  Every function
//! below is chosen to reach one of the affected paths: mutable borrows returned
//! across a join, mutable borrows carried through a loop, unit-returning
//! functions, and duplicated pure calls.

/// Plain mutable borrow: a backward function with one input and one output.
pub fn incr(x: &mut u32) {
    *x += 1;
}

/// A mutable borrow returned out of a branch: exercises the *join* path in
/// `abs_to_ty`, which the blanket makes monadic.
pub fn choose_mut<'a>(b: bool, x: &'a mut u32, y: &'a mut u32) -> &'a mut u32 {
    if b {
        x
    } else {
        y
    }
}

/// Consumes the joined borrow, so the continuation type shows up at a call site.
pub fn use_choose(b: bool) -> u32 {
    let mut x = 1;
    let mut y = 2;
    {
        let r = choose_mut(b, &mut x, &mut y);
        *r += 10;
    }
    x + y
}

/// A mutable borrow carried across loop iterations: exercises the *loop* path.
pub fn loop_incr(x: &mut u32, count: u32) {
    let mut index = 0;
    while index < count {
        incr(x);
        index += 1;
    }
}

/// Two identical pure subexpressions: `simplify_duplicate_calls` should still
/// merge them, since nothing here is effectful.
pub fn duplicate_calls(x: u32) -> u32 {
    let first = x + 1;
    let second = x + 1;
    first + second
}

/// A unit-returning function through a mutable borrow: `unit_vars_to_unit`
/// should still fire.
pub fn unit_result(x: &mut u32) {
    *x = 0;
}

/// Field-level mutable borrows. A tuple is used rather than a struct so that
/// both copies of this crate agree on the type and the two translations can be
/// compared directly in Lean.
pub fn swap_pair(p: &mut (u32, u32)) {
    let tmp = p.0;
    p.0 = p.1;
    p.1 = tmp;
}

/// A reborrow of a field, returned to the caller.
pub fn field_mut(p: &mut (u32, u32)) -> &mut u32 {
    &mut p.0
}

/// Nested backward functions: the caller must thread `field_mut`'s continuation.
pub fn bump_field(p: &mut (u32, u32)) -> u32 {
    {
        let f = field_mut(p);
        *f += 3;
    }
    p.0
}
