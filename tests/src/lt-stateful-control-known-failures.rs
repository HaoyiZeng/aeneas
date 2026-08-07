//@ [!lean] skip
//@ [lean] known-failure
//@ [lean] aeneas-args=-loops-to-rec
#![feature(register_tool)]
#![register_tool(verify)]
#![allow(dead_code, unused_variables, unused_mut)]

//! # Loop-local mutable-guard known failures
//!
//! Every fixture in this file independently reaches
//! `InterpBorrows.destructure_abs` (`interp/InterpBorrows.ml`, line 2076):
//! a mutable guard is updated through its `get_mut` backward from inside a
//! loop. They share one compiler root cause and are grouped intentionally.
//! Other loop failures are split by emitter into separate files.

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

    #[verify::opaque]
    pub fn try_write(&self) -> Option<WriteGuard<'_, T>> {
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
pub fn while_let_bounded_try_write(lock: &Lock<i32>, attempts: u32) -> u32 {
    let mut remaining = attempts;
    let mut successes = 0;
    while let Some(mut guard) = if remaining > 0 {
        Some(lock.write())
    } else {
        None
    } {
        *guard.get_mut() += 1;
        guard.release();
        successes += 1;
        remaining -= 1;
    }
    successes
}

#[verify::stateful_lifetimes]
pub fn while_let_genuine_try_write(lock: &Lock<i32>, attempts: u32) -> u32 {
    let mut remaining = attempts;
    let mut successes = 0;
    while let Some(mut guard) = lock.try_write() {
        *guard.get_mut() += 1;
        guard.release();
        successes += 1;
        remaining -= 1;
        if remaining == 0 {
            break;
        }
    }
    successes
}

#[verify::stateful_lifetimes]
pub fn acquire_release_each_iteration_while(lock: &Lock<i32>, n: u32) -> i32 {
    let mut i = 0;
    let mut total = 0;
    while i < n {
        let mut guard = lock.write();
        *guard.get_mut() += 1;
        total += *guard.get();
        guard.release();
        i += 1;
    }
    total
}

pub enum LoopGuardState<'a, T> {
    Idle,
    Holding(WriteGuard<'a, T>),
}

#[verify::stateful_lifetimes]
pub fn loop_state_adt_guard_cycle(lock: &Lock<i32>, n: u32) -> i32 {
    let mut state = LoopGuardState::Idle;
    let mut total = 0;
    for i in 0..n {
        state = match state {
            LoopGuardState::Idle => LoopGuardState::Holding(lock.write()),
            LoopGuardState::Holding(mut guard) => {
                *guard.get_mut() += i as i32;
                total += *guard.get();
                guard.release();
                LoopGuardState::Idle
            }
        };
    }
    if let LoopGuardState::Holding(guard) = state {
        guard.release();
    }
    total
}

#[verify::stateful_lifetimes('a)]
pub fn two_guards_ordered_in_loop<'a>(lock_a: &'a Lock<i32>, lock_b: &'a Lock<i32>, n: u32) -> i32 {
    let mut i = 0;
    let mut total = 0;
    while i < n {
        let mut ga = lock_a.write();
        let mut gb = lock_b.write();
        *ga.get_mut() += 1;
        *gb.get_mut() += 2;
        total += *ga.get() + *gb.get();
        gb.release();
        ga.release();
        i += 1;
    }
    total
}

#[verify::stateful_lifetimes]
pub fn guard_scope_inside_loop_body_block(lock: &Lock<i32>, n: u32) -> i32 {
    let mut total = 0;
    for i in 0..n {
        let doubled = (i as i32) * 2;
        {
            let mut guard = lock.write();
            *guard.get_mut() += doubled;
            total += *guard.get();
            guard.release();
        }
        total += 1;
    }
    total
}

#[verify::stateful_lifetimes]
pub fn unsupported_loop_invariant_optional_guard_shape(lock: &Lock<i32>, n: u32) -> i32 {
    let mut i = 0;
    let mut total = 0;
    while i < n {
        if let Some(mut guard) = lock.try_write() {
            *guard.get_mut() += 1;
            total += *guard.get();
            guard.release();
        } else {
            total -= 1;
        }
        i += 1;
    }
    total
}

#[verify::stateful_lifetimes]
pub fn unsupported_loop_divergent_exit_guard_state(lock: &Lock<i32>, n: u32) -> i32 {
    let mut i = 0;
    loop {
        let mut guard = lock.write();
        *guard.get_mut() += 1;
        if *guard.get() > 100 {
            return *guard.get();
        }
        guard.release();
        i += 1;
        if i >= n {
            break;
        }
    }
    -1
}
