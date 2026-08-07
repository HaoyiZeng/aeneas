//@ [!lean] skip
//! EXPECTED AFTER IMPLEMENTATION:
//! This file complements `lt-stateful-signatures.rs`, `lt-stateful-
//! reborrows.rs`, and `lt-stateful-wrappers.rs`. Where those files exercise
//! shapes the future "stateful lifetimes" feature is expected to *accept*
//! (with a documented, sound translation), every item in this file uses
//! `#[verify::stateful_lifetimes(...)]` with an argument that is expected
//! to be **semantically invalid** once the feature's argument checker
//! exists: an unknown lifetime name, an out-of-range index, a duplicate,
//! an annotation on a lifetime-free item, a bulk annotation on a
//! group/trait/impl, conflicting annotations, a malformed-but-token-valid
//! identifier, an ambiguous trait declaration, an anonymous-lifetime
//! reference, a stateful region with no backward input, a loop-escape
//! shape, a missing annotation on an otherwise-genuine acquire/release
//! shape, a sibling-method copy/paste mistake within one `impl` block, a
//! real (not merely hypothetical) mutually-recursive call-graph cycle
//! with only partial annotation, a type-alias lifetime collapse, stacked
//! bare-plus-named annotation forms, malformed attribute syntax, and
//! attributes attached to unsupported item/statement positions.
//!
//! Every case below is marked `EXPECTED FUTURE DIAGNOSTIC` in its doc
//! comment, describing the error the (not-yet-written) argument checker
//! should eventually report. **None of this is checked today.**
//!
//! CURRENT BASELINE:
//! `#[verify::stateful_lifetimes(...)]` is, today, an inert tool attribute:
//! it is registered via `#![register_tool(verify)]`, so rustc parses and
//! accepts *any* well-formed token tree as its argument list without
//! attaching any meaning to it, and Aeneas does not interpret it at all
//! yet (`Lock`/`ReadGuard`/`WriteGuard` are extracted as opaque calls, same
//! as in the other `lt-stateful-*.rs` fixtures). Consequently every
//! function in this file compiles and (would, if run) behave exactly as
//! written -- the invalidity described in each doc comment is *purely*
//! about the future meaning of the attribute argument, never about Rust
//! syntax or type-checking. This file must remain syntactically valid Rust
//! forever; only the semantics of the attribute arguments are wrong.
//!
//! **Exception -- the double-marked ancestor/descendant pair:** one case
//! originally planned for this file (a mutable reborrow nested inside an
//! already-acquired guard, both `'p` and `'c` marked at once) does *not*
//! merely translate as an inert opaque call today: it makes Aeneas's own
//! symbolic-to-pure pass abort (`Could not find var for symbolic value`),
//! which, under `-abort-on-error`, would take down extraction for this
//! entire file. Since every other case here must keep translating
//! end-to-end, that one case is quarantined in the companion
//! `lt-stateful-negative-known-failures.rs` fixture instead, which records
//! the crash as a genuine `known-failure`. See that file's module doc.
#![feature(register_tool)]
#![register_tool(verify)]

use std::marker::PhantomData;

#[verify::opaque]
pub struct Lock<T> {
    _marker: PhantomData<T>,
}

#[verify::opaque]
pub struct ReadGuard<'a, T> {
    _marker: PhantomData<&'a T>,
}

#[verify::opaque]
pub struct WriteGuard<'a, T> {
    _marker: PhantomData<&'a mut T>,
}

impl<T> Lock<T> {
    #[verify::opaque]
    pub fn new(_value: T) -> Self {
        unimplemented!()
    }

    #[verify::opaque]
    pub fn read(&self) -> ReadGuard<'_, T> {
        unimplemented!()
    }

    #[verify::opaque]
    pub fn write(&self) -> WriteGuard<'_, T> {
        unimplemented!()
    }
}

impl<'a, T> ReadGuard<'a, T> {
    #[verify::opaque]
    pub fn get(&self) -> &T {
        unimplemented!()
    }

    #[verify::opaque]
    pub fn release(self) {}
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

// ---------------------------------------------------------------------
// 1. Unknown lifetime name
// ---------------------------------------------------------------------

/// EXPECTED FUTURE DIAGNOSTIC: unknown lifetime name. `'z` does not name
/// any lifetime parameter of this function (only `'a` is declared); the
/// checker must reject a stateful-lifetime argument that doesn't resolve
/// to a parameter in scope, rather than silently ignoring it.
#[verify::stateful_lifetimes('z)]
pub fn unknown_lifetime_name<'a, T>(lock: &'a Lock<T>) -> WriteGuard<'a, T> {
    lock.write()
}

// ---------------------------------------------------------------------
// 2. Out-of-range index
// ---------------------------------------------------------------------

/// EXPECTED FUTURE DIAGNOSTIC: out-of-range positional index. This
/// function has exactly one input parameter (`lock`, position `0`). This
/// uses a hypothetical *positional* form of the attribute -- proposed here
/// only to test index validation, and not present in `lt-stateful-
/// signatures.rs` / `lt-stateful-reborrows.rs` / `lt-stateful-
/// wrappers.rs` -- where position `3` has no corresponding parameter and
/// must be rejected as out of range.
#[verify::stateful_lifetimes(3)]
pub fn out_of_range_index<T>(lock: &Lock<T>) -> WriteGuard<'_, T> {
    lock.write()
}

/// EXPECTED FUTURE DIAGNOSTIC: out-of-range index combined with a valid
/// named lifetime in the same attribute call. `'a` correctly names the
/// declared lifetime parameter, but `9` (the same speculative positional
/// form as `out_of_range_index` above) has no corresponding parameter --
/// this function only has one.
#[verify::stateful_lifetimes('a, 9)]
pub fn named_lifetime_and_out_of_range_index<'a, T>(lock: &'a Lock<T>) -> WriteGuard<'a, T> {
    lock.write()
}

// ---------------------------------------------------------------------
// 3. Duplicates
// ---------------------------------------------------------------------

/// EXPECTED FUTURE DIAGNOSTIC: duplicate lifetime token within a single
/// attribute invocation. `'a` is listed twice in the same argument list;
/// the checker must reject (or at least warn about) a stateful-lifetime
/// set with a repeated element rather than silently deduplicating it.
#[verify::stateful_lifetimes('a, 'a)]
pub fn duplicate_lifetime_in_one_call<'a, T>(lock: &'a Lock<T>) -> WriteGuard<'a, T> {
    lock.write()
}

/// EXPECTED FUTURE DIAGNOSTIC: duplicate annotation. The exact same
/// `#[verify::stateful_lifetimes('a)]` attribute is repeated twice
/// verbatim. Unlike `conflicting_annotations` below, the two copies agree
/// with each other, but repeating an annotation is still meaningless and
/// should be flagged rather than silently accepted.
#[verify::stateful_lifetimes('a)]
#[verify::stateful_lifetimes('a)]
pub fn duplicate_annotation_repeated<'a, T>(lock: &'a Lock<T>) -> WriteGuard<'a, T> {
    lock.write()
}

// ---------------------------------------------------------------------
// 4. Marking a no-lifetime function
// ---------------------------------------------------------------------

/// EXPECTED FUTURE DIAGNOSTIC: marking a function that has no lifetime
/// parameters -- and no references at all -- as having a stateful
/// lifetime. There is no borrow, guard, or region here for the annotation
/// to refer to.
#[verify::stateful_lifetimes]
pub fn marked_with_no_lifetime_at_all(a: i32, b: i32) -> i32 {
    a + b
}

// ---------------------------------------------------------------------
// 5. Marking a "pure group" (bulk annotation on impl/trait, not a fn)
// ---------------------------------------------------------------------

pub struct PlainPair {
    pub a: i32,
    pub b: i32,
}

/// EXPECTED FUTURE DIAGNOSTIC: bulk ("group") annotation on an `impl`
/// block. Every established fixture only ever attaches
/// `#[verify::stateful_lifetimes]` to individual `fn` items; there is no
/// notion of annotating an entire `impl` block at once, and neither method
/// below even acquires a guard, so treating them as a stateful group is
/// doubly wrong.
#[verify::stateful_lifetimes]
impl PlainPair {
    pub fn get_a(&self) -> i32 {
        self.a
    }

    pub fn set_b(&mut self, v: i32) {
        self.b = v;
    }
}

/// EXPECTED FUTURE DIAGNOSTIC: bulk annotation on a `trait` declaration (as
/// opposed to on one of its methods). Same issue as the `impl`-level case
/// above, at the trait-declaration granularity instead.
#[verify::stateful_lifetimes]
pub trait PlainOps {
    fn value(&self) -> i32;
}

// ---------------------------------------------------------------------
// 6. Conflicting annotations
// ---------------------------------------------------------------------

/// EXPECTED FUTURE DIAGNOSTIC: conflicting annotations. The same function
/// carries two `#[verify::stateful_lifetimes]` attributes disagreeing on
/// which lifetime is stateful (`'a` vs `'b`), even though the body
/// actually acquires and releases a guard under *both* lifetimes. The
/// checker must reject contradictory annotations on one item rather than
/// picking one arbitrarily.
#[verify::stateful_lifetimes('a)]
#[verify::stateful_lifetimes('b)]
pub fn conflicting_annotations<'a, 'b, T: Copy>(
    lock_a: &'a Lock<T>,
    lock_b: &'b Lock<T>,
) -> (T, T) {
    let ga = lock_a.read();
    let gb = lock_b.read();
    let va = *ga.get();
    let vb = *gb.get();
    ga.release();
    gb.release();
    (va, vb)
}

// ---------------------------------------------------------------------
// 7. Malformed-but-token-valid identifiers
// ---------------------------------------------------------------------

/// EXPECTED FUTURE DIAGNOSTIC: malformed-but-token-valid identifier.
/// `'static` is a perfectly valid *lifetime token*, but it is never a
/// generic parameter declared by this function -- it names the single
/// global lifetime, which cannot be "acquired" or "released" the way a
/// function-local stateful region can.
#[verify::stateful_lifetimes('static)]
pub fn malformed_identifier_static<T>(lock: &Lock<T>) -> WriteGuard<'_, T> {
    lock.write()
}

/// EXPECTED FUTURE DIAGNOSTIC: malformed-but-token-valid identifier,
/// second form. `'_a` is a legal *named* lifetime (distinct from the
/// anonymous placeholder `'_`), but its leading underscore makes it easy
/// to mistake for the anonymous-lifetime marker -- and it still does not
/// name any lifetime parameter declared by this function (only `'a` is
/// declared).
#[verify::stateful_lifetimes('_a)]
pub fn malformed_identifier_underscore_prefixed<'a, T>(lock: &'a Lock<T>) -> WriteGuard<'a, T> {
    lock.write()
}

// ---------------------------------------------------------------------
// 8. Trait declaration ambiguity
// ---------------------------------------------------------------------

/// EXPECTED FUTURE DIAGNOSTIC: trait-declaration ambiguity. Both methods
/// below independently declare their own, textually-identical `'a`
/// lifetime parameter (perfectly legal Rust: they are sibling
/// declarations, not nested scopes, so there is no shadowing error), yet
/// are annotated with the same lifetime name at the trait-declaration
/// level. It is ambiguous, at the level of the trait as a whole, whether
/// the two `'a` annotations are meant to refer to "the same" stateful
/// region across every implementor, or are independently scoped per
/// method -- the current grammar gives no way to tell.
pub trait AmbiguousLockable {
    type Item;

    #[verify::stateful_lifetimes('a)]
    fn acquire_write<'a>(&'a self) -> WriteGuard<'a, Self::Item>;

    #[verify::stateful_lifetimes('a)]
    fn acquire_read<'a>(&'a self) -> ReadGuard<'a, Self::Item>;
}

// ---------------------------------------------------------------------
// 9. Anonymous lifetime name use
// ---------------------------------------------------------------------

/// EXPECTED FUTURE DIAGNOSTIC: anonymous lifetime name use. `'_` is the
/// placeholder for an elided lifetime, not the name of a declared
/// parameter; using it as an explicit attribute argument doesn't identify
/// any specific region for the checker to act on.
#[verify::stateful_lifetimes('_)]
pub fn anonymous_lifetime_reference<T>(lock: &Lock<T>) -> ReadGuard<'_, T> {
    lock.read()
}

/// EXPECTED FUTURE DIAGNOSTIC: anonymous lifetime mixed with a named one
/// in the same attribute call. Even granting that `'_` might someday be
/// accepted as shorthand for "the sole elided lifetime", mixing it with an
/// explicitly named lifetime in the same list is not well-defined when the
/// function (as here) has two independent input lifetimes -- there is no
/// canonical way to say which one `'_` should mean.
#[verify::stateful_lifetimes('a, '_)]
pub fn anonymous_and_named_mixed<'a, T: Copy, U: Copy>(
    lock_a: &'a Lock<T>,
    lock_b: &Lock<U>,
) -> (T, U) {
    let ga = lock_a.read();
    let gb = lock_b.read();
    let va = *ga.get();
    let vb = *gb.get();
    ga.release();
    gb.release();
    (va, vb)
}

// ---------------------------------------------------------------------
// 10. Stateful region with no backward input
// ---------------------------------------------------------------------

/// EXPECTED FUTURE DIAGNOSTIC: stateful region with no backward input.
/// `'a` here is an ordinary *shared* borrow with no guard/lock anywhere in
/// sight -- exactly the kind of borrow that, per `lt-stateful-
/// signatures.rs`, never gets a backward function at all. Marking it
/// stateful claims a release-style backward function that this function
/// has no way to produce.
#[verify::stateful_lifetimes('a)]
pub fn shared_borrow_marked_stateful<'a>(x: &'a i32) -> &'a i32 {
    x
}

// ---------------------------------------------------------------------
// 11. Ancestor/descendant double stateful
// ---------------------------------------------------------------------
//
// MOVED to `lt-stateful-negative-known-failures.rs`: today's baseline
// (the attribute is inert, see the file's module doc) does not merely
// treat this case as an ordinary opaque call like every other case in
// this file -- it makes Aeneas's symbolic-to-pure translation pass abort
// entirely on this function (`Could not find var for symbolic value`,
// `SymbolicToPureCore.ml`), which brings down extraction for the *whole
// file* (`-abort-on-error`). Since this file must remain translatable end
// to end today, the case is quarantined in a dedicated `known-failure`
// whole-file fixture instead. See that file's module doc for the full
// explanation of the shape and why it crashes today.

// ---------------------------------------------------------------------
// 12. Loop escape marker
// ---------------------------------------------------------------------

/// EXPECTED FUTURE DIAGNOSTIC: loop-escape marker. The guard is acquired
/// before the loop; on one control-flow path (the early `return` inside
/// the `for` loop) it escapes the function *without* ever reaching
/// `guard.release()` at all. The `'a` annotation gives no way to express
/// that this control-flow edge bypasses the release that the "one guard,
/// one release" model (see e.g. `write_guard_release_only` in
/// `lt-stateful-signatures.rs`) otherwise relies on.
#[verify::stateful_lifetimes('a)]
pub fn guard_may_escape_loop<'a, T: Copy + PartialEq>(
    lock: &'a Lock<T>,
    needle: T,
    haystack: &[T],
) -> Option<T> {
    let guard = lock.write();
    for candidate in haystack {
        if *candidate == needle {
            return Some(*guard.get()); // guard.release() never reached on this path
        }
    }
    guard.release();
    None
}

// ---------------------------------------------------------------------
// 13. Missing annotation on a genuine acquire/release shape
// ---------------------------------------------------------------------

/// EXPECTED FUTURE DIAGNOSTIC: missing annotation. This function's body is
/// structurally identical to `minimal_write_acquire_release` in
/// `lt-stateful-signatures.rs` -- it acquires a write guard and releases
/// it, nothing else -- yet it carries no `#[verify::stateful_lifetimes]`
/// attribute at all. Today, with the attribute inert, this is simply
/// translated like any other opaque call and happens to be sound by
/// accident; once the feature exists, a function that plainly follows the
/// acquire/.../release shape but was never opted in should be flagged
/// (e.g. as a "did you forget the attribute?" diagnostic), rather than
/// silently kept on the old, non-stateful translation path forever.
pub fn unannotated_acquire_release<T>(lock: &Lock<T>) {
    let guard = lock.write();
    guard.release();
}

// ---------------------------------------------------------------------
// 14. Sibling-method copy/paste lifetime
// ---------------------------------------------------------------------

/// A struct wrapping a `Lock<T>`, used below to show a copy/paste mistake
/// between two sibling methods on the same `impl` block.
pub struct Toggle<T> {
    inner: Lock<T>,
}

impl<T: Copy> Toggle<T> {
    /// The genuine stateful wrapper: `'a` really is the lock's borrow/guard
    /// lifetime here.
    #[verify::stateful_lifetimes('a)]
    pub fn acquire_write<'a>(&'a self) -> WriteGuard<'a, T> {
        self.inner.write()
    }

    /// EXPECTED FUTURE DIAGNOSTIC: sibling-method copy/paste. This
    /// `#[verify::stateful_lifetimes('a)]` annotation was evidently
    /// copy-pasted verbatim from `acquire_write` immediately above --
    /// both methods declare a parameter lifetime spelled `'a`, so the name
    /// resolves without complaint (sibling methods are independently
    /// scoped, so reusing the name is legal Rust, just as in
    /// `AmbiguousLockable` above) -- but here `'a` denotes an ordinary
    /// *pure* shared borrow of `flag`, not a lock/guard lifetime at all:
    /// there is no call to `Lock::read`/`Lock::write` anywhere in this
    /// method's body. Marking `'a` stateful claims a release backward
    /// function this method has no way to produce -- the same underlying
    /// mistake as `shared_borrow_marked_stateful` above, but arrived at by
    /// copying a *correct* sibling annotation rather than by writing an
    /// incorrect one from scratch. The checker cannot assume that textual
    /// repetition of a working annotation implies semantic validity; each
    /// method must be re-validated independently.
    #[verify::stateful_lifetimes('a)]
    pub fn peek<'a>(&'a self, flag: &'a bool) -> bool {
        *flag
    }
}

// ---------------------------------------------------------------------
// 15. Real (not hypothetical) SCC with only partial marking
// ---------------------------------------------------------------------

/// One half of a genuinely mutually-recursive pair (a real strongly
/// connected component in the call graph, not merely a hypothetical one):
/// `ping` calls `pong`, and `pong` (below) calls `ping` right back.
/// Annotated normally.
#[verify::stateful_lifetimes('a)]
pub fn ping<'a, T: Copy>(lock: &'a Lock<T>, n: u32) -> T {
    let guard = lock.write();
    let v = *guard.get();
    guard.release();
    if n == 0 {
        v
    } else {
        pong(lock, n - 1)
    }
}

/// EXPECTED FUTURE DIAGNOSTIC: real SCC with only partial annotation.
/// `pong` is mutually recursive with `ping` above -- together they form one
/// strongly connected component in the call graph -- and `pong`'s body has
/// the exact same acquire/release shape as `ping`'s, yet `pong` carries no
/// `#[verify::stateful_lifetimes]` attribute at all. Unlike
/// `unannotated_acquire_release` (section 13), whose problem is purely
/// local to one function, this case is about *consistency within a cycle*:
/// the two functions cannot be checked independently of each other (each
/// one's own guard/release reasoning depends on what the other does across
/// the recursive call), so annotating only one member of a real,
/// non-hypothetical SCC and leaving the other bare is a shape the checker
/// must reject rather than resolve function-by-function.
pub fn pong<T: Copy>(lock: &Lock<T>, n: u32) -> T {
    let guard = lock.write();
    let v = *guard.get();
    guard.release();
    if n == 0 {
        v
    } else {
        ping(lock, n - 1)
    }
}

// ---------------------------------------------------------------------
// 16. Type-alias lifetime collapse
// ---------------------------------------------------------------------

/// A struct nesting *two* independently-acquired write guards side by
/// side, each with its own lifetime parameter.
pub struct PairGuardBox<'p, 'q, T> {
    pub first: WriteGuard<'p, T>,
    pub second: WriteGuard<'q, T>,
}

/// A type alias that collapses `PairGuardBox`'s two independent lifetime
/// parameters (`'p` and `'q`) onto a single name `'r`.
pub type CollapsedGuardBox<'r, T> = PairGuardBox<'r, 'r, T>;

/// EXPECTED FUTURE DIAGNOSTIC: alias collapse. `CollapsedGuardBox<'r, T>`
/// aliases `PairGuardBox<'r, 'r, T>`, collapsing what are, in the aliased
/// struct, two independently-acquired guard lifetimes onto a single name
/// `'r`. Once the alias is resolved down to the underlying struct type --
/// as the checker must do, per `acquire_via_alias` in
/// `lt-stateful-wrappers.rs` -- `'r` turns out to name *two* simultaneously
/// live guards at once, not one. Marking `'r` stateful is therefore
/// ambiguous: does the annotation claim to manage `first`'s guard,
/// `second`'s guard, or (incorrectly) both under a single release?
#[verify::stateful_lifetimes('r)]
pub fn wrap_collapsed<'r, T>(
    first: WriteGuard<'r, T>,
    second: WriteGuard<'r, T>,
) -> CollapsedGuardBox<'r, T> {
    CollapsedGuardBox { first, second }
}

// ---------------------------------------------------------------------
// 17. Named form with no lifetime
// ---------------------------------------------------------------------

/// EXPECTED FUTURE DIAGNOSTIC: named-list form on a function with no
/// lifetime parameters at all. Companion to `marked_with_no_lifetime_at_all`
/// above (which uses the bare form): here the named-list form is used
/// instead, naming a lifetime `'x` that cannot exist because the function
/// declares none -- the same underlying mistake, reached through the other
/// half of the canonical bare/named-list attribute syntax.
#[verify::stateful_lifetimes('x)]
pub fn named_form_with_no_lifetime_at_all(a: i32, b: i32) -> i32 {
    a + b
}

// ---------------------------------------------------------------------
// 18. Conflicting annotation forms stacked on one item
// ---------------------------------------------------------------------

/// EXPECTED FUTURE DIAGNOSTIC: conflicting annotation *forms* on one item.
/// The bare form and the named-list form are both attached to the same
/// function. Even though `'a` is this function's only lifetime parameter
/// -- so the bare form and the named form would, if each were used alone,
/// agree on which lifetime is meant -- stacking both forms on one item is
/// still a meaningless double-specification. Unlike
/// `duplicate_annotation_repeated` above (the same form repeated
/// verbatim), this mixes the two canonical forms of the attribute; the
/// checker must reject the combination rather than treat it as trivially
/// consistent just because it happens not to disagree on content.
#[verify::stateful_lifetimes]
#[verify::stateful_lifetimes('a)]
pub fn bare_and_named_conflict<'a, T>(lock: &'a Lock<T>) -> WriteGuard<'a, T> {
    lock.write()
}

// ---------------------------------------------------------------------
// 19. Malformed forms and unsupported attachment positions
// ---------------------------------------------------------------------

/// EXPECTED FUTURE DIAGNOSTIC: parenthesized empty list. This is not the
/// bare form; it explicitly selects zero lifetimes.
#[verify::stateful_lifetimes()]
pub fn empty_parenthesized_list<'a, T>(lock: &'a Lock<T>) -> WriteGuard<'a, T> {
    lock.write()
}

/// EXPECTED FUTURE DIAGNOSTIC: name-value syntax is not one of the
/// canonical bare/named-list forms.
#[verify::stateful_lifetimes = "'a"]
pub fn name_value_attribute_form<'a, T>(lock: &'a Lock<T>) -> WriteGuard<'a, T> {
    lock.write()
}

/// EXPECTED FUTURE DIAGNOSTIC: a string literal is not a Rust lifetime
/// token, even though the tool-attribute token tree is syntactically valid.
#[verify::stateful_lifetimes("a")]
pub fn string_literal_attribute_form<'a, T>(lock: &'a Lock<T>) -> WriteGuard<'a, T> {
    lock.write()
}

/// EXPECTED FUTURE DIAGNOSTIC: the verification attribute belongs on
/// functions/methods, not on a type declaration.
#[verify::stateful_lifetimes]
pub struct AttributeOnStruct<'a, T> {
    marker: PhantomData<&'a T>,
}

/// EXPECTED FUTURE DIAGNOSTIC: type aliases cannot declare effectful
/// backward applications.
#[verify::stateful_lifetimes('a)]
pub type AttributeOnAlias<'a, T> = &'a T;

/// EXPECTED FUTURE DIAGNOSTIC: statement-level attachment has no function
/// signature whose lifetime set can be recorded.
pub fn attribute_on_statement<'a, T>(lock: &'a Lock<T>) {
    #[verify::stateful_lifetimes]
    let guard = lock.read();
    guard.release();
}
