//@ [!lean] skip
//@ [lean] known-failure
//! # Stateful lock/guard lifetime fixtures — UNWIND variant
//!
//! This file was split out of `lt-stateful-failures.rs`. That file
//! documents Rust-level failure sources (`panic!`, `assert!`, integer
//! overflow, out-of-bounds indexing, division/remainder by zero,
//! `Option::unwrap`, `Result::?`) that all translate faithfully to the Lean
//! `fail` case of the `Result` monad (or, for `Err`/`None`, to an ordinary
//! `ok`-wrapped value — see that file's module docs for why those two are
//! *not* the same thing). `catch_unwind` is different in kind and currently
//! fails Aeneas's internal type checks, so it lives here as a focused
//! known-failure. `std::process::abort` does translate; its baseline model
//! is recorded in `lt-stateful-failures.rs`.
//!
//! ## EXPECTED / CURRENT
//! - [`catch_unwind_candidate`] — Rust's unwind-based panic recovery has no
//!   counterpart in the `Result`-monad translation; Aeneas cannot
//!   distinguish "this call may unwind and be caught by the caller" from
//!   an ordinary `fail`, so a spec for this function would either be
//!   unsound or require treating `catch_unwind` itself as an opaque call —
//!   at which point the distinction between "panicked and was caught" and
//!   "returned normally" is lost entirely. This function is not expected
//!   to be verified faithfully (if at all).
//! CURRENT compiler failure: with `-checks`, Aeneas reports an invariant
//! violation in `interp/Invariants.ml`, line 422.
//!
//! This function uses no opaque lock/guard vocabulary from the
//! sibling `lt-stateful-*.rs` files: both hazards are orthogonal to guard
//! lifetimes, so there is nothing to gain by threading a `Lock`/`Guard`
//! through them, and keeping this file's vocabulary minimal keeps the
//! `known-failure` surface as small and easy to audit as possible.

#![feature(register_tool)]
#![register_tool(verify)]

/// **Documented Aeneas limitation** (see module docs above): `catch_unwind`
/// models Rust's unwind-based recovery, which has no equivalent in the
/// `Result`-monad translation. EXPECTED/CURRENT: this function is not
/// expected to be verified faithfully; at best Aeneas would need to treat
/// `catch_unwind` itself as an opaque call, at which point the distinction
/// between "panicked and was caught" and "returned normally" is lost.
pub fn catch_unwind_candidate(x: u32, divisor: u32) -> u32 {
    match std::panic::catch_unwind(move || x / divisor) {
        Ok(v) => v,
        Err(_) => 0,
    }
}
