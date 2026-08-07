//@ [!lean] skip
//@ [lean] known-failure
#![feature(register_tool)]
#![register_tool(verify)]
#![allow(dead_code, unused_variables)]
//! # Stateful-lifetimes negative-argument suite -- known-failure spinoff
//!
//! Companion to `lt-stateful-negative.rs` (same
//! `#[verify::stateful_lifetimes(...)]` vocabulary and rationale -- see
//! that file's module doc for the general background: every item there
//! uses the attribute with an argument that is expected to be
//! **semantically invalid** once the feature's argument checker exists,
//! while remaining ordinary, opaque-call-translatable Rust *today* since
//! the attribute is currently inert). That file requires every one of its
//! cases to translate successfully today, since it is meant to keep
//! extracting end-to-end as a single whole-file baseline. This file
//! exists to hold the one shape from that suite which does *not* meet
//! that bar -- i.e. a genuine `//@ known-failure` per `tests/README.md`,
//! which records the `aeneas` tool's own error output rather than
//! generated backend code.
//!
//! ## EXPECTED (once the future stateful-lifetimes argument checker exists)
//! A double-marked ancestor/descendant pair -- the same lifetime-position
//! shape as `project_nested_guard` in
//! `lt-stateful-wrapper-projection-known-failures.rs` (a mutable
//! reborrow of a field nested inside an already-acquired guard), except
//! that *both* the ancestor lifetime (`'p`, the fixed type parameter under
//! which the nested guard was acquired by some earlier caller) and the
//! descendant lifetime (`'c`, the fresh reborrow of the wrapper produced
//! by this function) are marked stateful in the same annotation -- should
//! be rejected by the checker: marking `'p` here double-counts a resource
//! this function neither acquired nor releases, on top of the one
//! genuinely local resource named by `'c`.
//!
//! ## CURRENT
//! Every *other* case in `lt-stateful-negative.rs` translates today as an
//! ordinary opaque call, exactly like the corresponding "genuine" shapes
//! in `lt-stateful-signatures.rs` / `lt-stateful-reborrows.rs` /
//! `lt-stateful-wrappers.rs` -- the inert attribute changes nothing about
//! how Aeneas sees the function. This one case is different: passing it
//! through Aeneas's symbolic-to-pure translation pass makes the compiler
//! itself abort with an internal error,
//! ```text
//! [Error] Could not find var for symbolic value: 7
//! Source: 'tests/src/lt-stateful-negative-known-failures.rs', lines ...
//! Compiler source: symbolic/SymbolicToPureCore.ml, line 520
//! ```
//! i.e. a genuine Aeneas bug unrelated to the (not-yet-written) argument
//! checker: today's `SymbolicToPureCore` pass fails to look up the
//! symbolic value produced when ending the borrow of the reborrowed
//! `&'c mut T` returned from a nested-guard projection
//! (`wrapper.guard.get_mut()`), where the outer mutable reference itself
//! points into a struct with its own (already-instantiated) lifetime
//! parameter `'p`. Since `-abort-on-error` makes any single crashing
//! function take down extraction for its *entire* file, this shape cannot
//! live alongside the other (successfully translating) cases in
//! `lt-stateful-negative.rs` -- it is quarantined here instead, as its own
//! whole-file `known-failure` fixture, with only the minimal scaffolding
//! (the `WriteGuard`/`GuardBox` shape) needed to reproduce the crash.
//!
//! **If this ever stops crashing** (i.e.
//! `make test-lt-stateful-negative-known-failures.rs` starts producing a
//! clean, non-error `.out` file), that means Aeneas's symbolic-to-pure
//! pass now handles this reborrow-through-a-lifetime-parameterized-struct
//! shape: remove the `known-failure` marker, move
//! `ancestor_and_descendant_both_marked` (and its supporting `GuardBox`
//! struct) back into `lt-stateful-negative.rs` as case 11
//! ("Ancestor/descendant double stateful"), and update that file's module
//! doc and case list accordingly.

use std::marker::PhantomData;

#[verify::opaque]
pub struct WriteGuard<'a, T> {
    _marker: PhantomData<&'a mut T>,
}

impl<'a, T> WriteGuard<'a, T> {
    #[verify::opaque]
    pub fn get_mut(&mut self) -> &mut T {
        unimplemented!()
    }
}

/// A struct nesting an already-acquired guard (same shape as `GuardBox` in
/// `lt-stateful-wrappers.rs`).
pub struct GuardBox<'p, T> {
    pub guard: WriteGuard<'p, T>,
}

/// EXPECTED FUTURE DIAGNOSTIC: ancestor/descendant double stateful
/// marking. `'c` is the genuinely live, freshly-derived subborrow region
/// in this function (the reborrow of `wrapper`); `'p` is merely a *fixed*
/// type parameter of `GuardBox` here -- the guard it names was acquired,
/// and will be released, by whichever caller produced the `GuardBox` in
/// the first place, not by this function. Marking both `'p` (the
/// ancestor) and `'c` (the descendant) as independently stateful in the
/// very same annotation double-counts a single already-acquired resource
/// as though two separate guards were being managed here. Contrast with
/// `project_nested_guard` in
/// `lt-stateful-wrapper-projection-known-failures.rs`, which carries no
/// stateful annotation because it is only a pure reborrow.
///
/// CURRENT: see the module doc above -- this crashes Aeneas's
/// symbolic-to-pure pass today, unrelated to the future argument checker.
#[verify::stateful_lifetimes('p, 'c)]
pub fn ancestor_and_descendant_both_marked<'c, 'p, T>(
    wrapper: &'c mut GuardBox<'p, T>,
) -> &'c mut T {
    wrapper.guard.get_mut()
}
