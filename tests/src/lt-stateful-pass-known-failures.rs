//@ [!lean] skip
//@ [lean] known-failure
#![feature(register_tool)]
#![register_tool(verify)]
#![allow(dead_code, unused_variables, unused_mut)]

//! # Stateful optimizer suite — loop-break known failure
//!
//! Companion to `lt-stateful-passes.rs`. Higher-ranked closure literals
//! returning mutable borrows live in
//! `lt-stateful-pass-backend-failures.rs`: Aeneas translates them, but
//! their generated Lean does not elaborate. This file contains the one
//! remaining
//! compiler failure from the optimizer corpus: a `for` loop whose body
//! performs opaque effects and exits with `break`.
//!
//! EXPECTED: `loop_break_preserves_order` performs acquire/release exactly
//! `min(stop_at + 1, n)` times. The break must stop future effects and must
//! not permit effects to be hoisted before its condition.
//!
//! CURRENT: Aeneas reports:
//! ```text
//! [Error] Could not match the contexts
//! Source: 'tests/src/lt-stateful-pass-known-failures.rs', lines 1:0-...
//! Compiler source: interp/InterpJoin.ml, line 1542
//! ```
//! The loop-join context matcher cannot reconcile the `break` exit with the
//! loop back-edge. Once this test generates successfully, move the function
//! into the normal suite's loop section.

#[verify::opaque]
pub struct Lock {
    _priv: (),
}

impl Lock {
    #[verify::opaque]
    pub fn acquire(&self) -> Guard<'_> {
        unimplemented!()
    }

    #[verify::opaque]
    pub fn release(&self, guard: Guard<'_>) {
        unimplemented!()
    }
}

#[verify::opaque]
pub struct Guard<'a> {
    _lock: &'a Lock,
}

pub fn loop_break_preserves_order(l: &Lock, n: usize, stop_at: usize) -> usize {
    let mut count = 0;
    for i in 0..n {
        let g = l.acquire();
        l.release(g);
        count += 1;
        if i == stop_at {
            break;
        }
    }
    count
}
