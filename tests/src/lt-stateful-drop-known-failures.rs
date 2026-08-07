//@ [!lean] skip
//@ [lean] known-failure
#![feature(register_tool)]
#![register_tool(verify)]

//! Known baseline failure isolated from `lt-stateful-temporaries.rs` (the
//! guard-family companion to `lt-stateful-drop.rs`, which covers named
//! bindings / structural scoping, while `lt-stateful-temporaries.rs` covers
//! unnamed temporaries).
//!
//! ## Root cause
//!
//! Both `lt-stateful-drop.rs` and `lt-stateful-temporaries.rs` originally
//! failed entirely (`Can't retrieve the variants of non-adt type: Guard`,
//! raised from
//! `Charon__Substitute.type_decl_get_instantiated_variants_fields_types`,
//! via `Aeneas__InterpExpansion.compute_expanded_symbolic_non_builtin_adt_value`)
//! because each file's `Drop::drop` method was written as a *transparent*
//! body (`release(self.lock)`/`release_exclusive(self.lock)`)
//! reaching into the private field of an `#[verify::opaque]`-marked
//! `Guard` struct. Aeneas has no visibility into an opaque type's fields,
//! so evaluating that field access crashes symbolic expansion for *every*
//! function that (implicitly or explicitly) drops a `Guard` -- i.e. nearly
//! every fixture in both files. The fix (applied directly to
//! `lt-stateful-drop.rs` and `lt-stateful-temporaries.rs`) is the same
//! convention now used by those fixtures: mark the `drop` method itself
//! `#[verify::opaque]` and give it an `unimplemented!()` body. An attribute
//! on the `impl Drop` block is inert for Aeneas.
//!
//! That fix alone makes every fixture in `lt-stateful-drop.rs` generate
//! cleanly. `lt-stateful-temporaries.rs` has one further, independent
//! baseline gap, isolated here: its (deliberately) non-opaque
//! `Guard::items` method, which returns `self.items.iter()` so that
//! `for_loop_head_temporary` below can demonstrate a `for`-loop iterator
//! that genuinely borrows from the guard (not just a `Copy` value derived
//! from it). Since `Guard` itself is `#[verify::opaque]`, Aeneas has no
//! field information for it -- so a transparent method reaching into
//! `self.items` hits the exact same "Can't retrieve the variants of
//! non-adt type: Guard" crash, independent of (and not fixed by) the
//! `Drop`-impl fix above. This one fixture -- and only this one -- is
//! genuinely baseline-incompatible; every other fixture in
//! `lt-stateful-temporaries.rs` (including the contrasting
//! `for_loop_body_guard_per_iteration`, which never calls `Guard::items`)
//! generates successfully and stays in that file.
//!
//! ## EXPECTED (once fixed)
//! The Reference's desugaring of `for PAT in iter_expr { body }` wraps
//! `iter_expr` in an outer `match IntoIterator::into_iter(iter_expr) { mut
//! iter => loop { ... } }`, with the explicit note: "The outer match is
//! used to ensure that any temporary values in `iter_expr` don't get
//! dropped before the loop is finished." Since `lock.acquire()` here is
//! evaluated as part of `iter_expr` (as the receiver of `.items()`), the
//! `Guard` temporary it produces should be held for the *entire* loop,
//! across all iterations -- not re-acquired/released per iteration. With a
//! real mutex this is the textbook footgun: `for x in
//! mutex.lock().unwrap().iter() { ... }` holds the lock for the whole loop
//! body, which can deadlock on a reentrant acquire inside the loop.
//!
//! This crash escapes as an uncaught exception on stderr, so the checked-in
//! `.lean.out` contains only the preceding `Imported` line. The trip-wire is
//! therefore the process exit status / appearance of generated Lean, not the
//! `.out` contents. **If this test ever exits successfully**, Aeneas can now
//! expand symbolic values
//! of a type marked `#[verify::opaque]` well enough to support a
//! transparent method borrowing one of its private fields: remove the
//! `known-failure` marker, move `Guard::items` and `for_loop_head_temporary`
//! back into `lt-stateful-temporaries.rs`, and update that file's module
//! doc and `while_let_temporary` / `for_loop_body_guard_per_iteration` doc
//! comments (which currently point here) accordingly.

// ---------------------------------------------------------------------
// Minimal opaque Lock / Guard prelude
// ---------------------------------------------------------------------
//
// Duplicated (rather than shared) from `lt-stateful-temporaries.rs`,
// trimmed to exactly what `for_loop_head_temporary` needs: `Lock`, a
// `Guard` with a real payload field, `acquire`, and the one non-opaque
// method (`items`) that reproduces the crash. No `Drop` impl is needed
// here -- this reproducer never reaches drop-scope evaluation. The crash is
// triggered while translating `Guard::items`'s transparent `self.items`
// field access; the `for` loop is only the consumer of that method.

/// An opaque handle to an external synchronization primitive.
#[verify::opaque]
pub struct Lock;

/// An opaque RAII guard representing exclusive ownership of a `Lock`.
#[verify::opaque]
pub struct Guard<'a> {
    lock: &'a Lock,
    /// Dummy payload so `items()` below has something real to iterate over,
    /// which lets `for_loop_head_temporary` demonstrate an iterator that
    /// genuinely borrows from the guard (not just a `Copy` value derived
    /// from it).
    items: [u32; 3],
}

impl Lock {
    /// EXPECTED: an "acquire" event for `self`; the matching "release" event
    /// happens exactly when the returned `Guard` is dropped.
    #[verify::opaque]
    pub fn acquire(&self) -> Guard<'_> {
        unimplemented!()
    }
}

impl<'a> Guard<'a> {
    /// Deliberately **not** `#[verify::opaque]`: this needs a real field
    /// access to return an iterator that actually borrows `self`, for
    /// `for_loop_head_temporary` below. This is exactly what currently
    /// crashes Aeneas -- see the module doc above.
    pub fn items(&self) -> std::slice::Iter<'_, u32> {
        self.items.iter()
    }
}

fn touch_item(_x: u32) {}

// ---------------------------------------------------------------------
// `for` loop head expression temporary (the classic guard footgun)
// ---------------------------------------------------------------------

/// EXPECTED: this is the single most important -- and most surprising --
/// pattern in `lt-stateful-temporaries.rs`'s "for loop head expression"
/// family. See the module doc above for why it currently crashes instead
/// of translating, and the "EXPECTED (once fixed)" section for the
/// intended acquire/release behavior. Contrast with
/// `for_loop_body_guard_per_iteration` in `lt-stateful-temporaries.rs`,
/// where the guard is acquired *inside* the loop body instead.
#[verify::stateful_lifetimes]
pub fn for_loop_head_temporary(lock: &Lock) {
    for x in lock.acquire().items() {
        touch_item(*x);
    }
}
