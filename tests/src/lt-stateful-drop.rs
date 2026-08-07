//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]

//! Fixtures for drop / lifetime placement of **opaque stateful guards**
//! (think `MutexGuard`, `RwLockReadGuard`, a file-descriptor guard, ...).
//!
//! ## Purpose
//!
//! Every function below acquires one or more [`Guard`] / [`ReadGuard`]
//! values from an opaque [`Lock`] and exercises a specific Rust binding /
//! scoping construct (explicit `drop`, nested scopes, shadowing, `Option`,
//! `take`/`replace`, `swap`, destructuring, ...). Each function's doc
//! comment states the **EXPECTED** acquire/release ordering -- i.e. what a
//! (hypothetical, not-yet-implemented) `stateful_lifetimes` verification
//! pass should conclude by tracking the guard's constructor ("acquire") and
//! its `Drop` impl ("release") through ordinary Rust drop-scope rules.
//!
//! CURRENT BASELINE:
//! `#[verify::stateful_lifetimes]` is a **tentative** marker attribute: it
//! is registered via `#![register_tool(verify)]` so that `rustc` accepts it.
//! Unlike `#[verify::opaque]` and `#[verify::test]` (both of which Charon
//! special-cases in `parse_special_attr` and accepts silently), `verify::
//! stateful_lifetimes` is not yet one of the names Charon recognizes there;
//! falling through to the `_ => None` arm turns it into an `Unrecognized
//! attribute` error, which `register_error!` reports at
//! `Level::WARNING` -- so, today, Charon emits one such warning per fixture
//! in this file, not silence. It exists purely to identify, today, which
//! functions are meant as fixtures for that future pass -- the same way
//! `#[verify::test]` marks functions that today generate `#assert` checks.
//! Every fixture in this file is required to be **valid, borrow-checked
//! Rust**: none of them are ever actually called (there is no `main`, no
//! `#[verify::test]`), since the guards are opaque and their
//! "acquire"/"release" side effects are unimplemented stubs. A handful of
//! genuinely *unsupported* patterns (constructs that would not even
//! borrow-check) are documented as inert comments near the bottom of
//! the file rather than included as compiled code.
//!
//! The release points described below are **aspirational under the current
//! baseline**: Aeneas does not emit implicit end-of-scope `Drop::drop` glue,
//! and `core::mem::drop` does not dispatch the opaque destructor. Generated
//! Lean therefore records acquire/data-flow structure, not the release
//! events themselves. In addition, `simplify_duplicate_calls` currently
//! merges repeated structurally identical opaque acquires; affected fixtures
//! are labeled `CURRENT (BUG)` below.

// ---------------------------------------------------------------------
// Opaque Lock / Guard prelude
// ---------------------------------------------------------------------

/// An opaque handle to an external synchronization primitive (e.g. a mutex,
/// a spinlock, a file lock, ...). We never construct a `Lock` in this file:
/// every fixture receives one (or more) already borrowed as a parameter,
/// since these fixtures are never executed -- only ever type/borrow-checked.
#[verify::opaque]
pub struct Lock;

/// An opaque RAII guard representing **exclusive** ownership of a `Lock`.
/// Its `Drop` impl below models the (opaque) "release" side effect that a
/// real mutex guard performs when it goes out of scope.
#[verify::opaque]
pub struct Guard<'a> {
    lock: &'a Lock,
}

/// An opaque RAII guard representing one of possibly many concurrent
/// **shared** acquisitions of a `Lock` (think `RwLock::read`).
#[verify::opaque]
pub struct ReadGuard<'a> {
    lock: &'a Lock,
}

impl Lock {
    /// EXPECTED: calling `acquire` is an "acquire" event for `self`. The
    /// returned `Guard` borrows `self` for as long as it is alive; the
    /// matching "release" event happens exactly when the `Guard` is
    /// dropped (see the `Drop for Guard` impl below).
    #[verify::opaque]
    pub fn acquire(&self) -> Guard<'_> {
        unimplemented!()
    }

    /// EXPECTED: like `acquire`, but shared -- many `ReadGuard`s borrowed
    /// from the same `Lock` may be alive at once.
    #[verify::opaque]
    pub fn read(&self) -> ReadGuard<'_> {
        unimplemented!()
    }
}

/// EXPECTED release point: wherever ordinary Rust drop-scope rules say
/// this `Guard` value's scope ends (NOT necessarily the lexical block
/// it was written in -- see e.g. `block_expr_returns_guard` below).
///
/// The `drop` method itself must be `#[verify::opaque]`:
/// `Guard` is an opaque struct, so Aeneas has no visibility into its
/// (private) `lock` field, and a transparent `drop` body cannot access it
/// (this is the same convention used by `AutoGuard`/`Arc` in
/// `lt-stateful-passes.rs` and `lt-stateful-arc.rs`).
impl<'a> Drop for Guard<'a> {
    #[verify::opaque]
    fn drop(&mut self) {
        unimplemented!()
    }
}

/// See the `impl Drop for Guard` doc comment above -- same rationale.
impl<'a> Drop for ReadGuard<'a> {
    #[verify::opaque]
    fn drop(&mut self) {
        unimplemented!()
    }
}

/// A plain (non-opaque) aggregate of two exclusive guards borrowed from the
/// same lifetime, used only to demonstrate struct-pattern destructuring
/// drop order below.
pub struct GuardPair<'a> {
    first: Guard<'a>,
    second: Guard<'a>,
}

/// A tuple-struct twin of `GuardPair`, used only to demonstrate
/// tuple-struct partial-move drop order (`tuple_struct_partial_move`
/// below), as opposed to `GuardPair`'s named-field partial move
/// (`partial_aggregate_move`).
pub struct GuardTuplePair<'a>(Guard<'a>, Guard<'a>);

// --- small "use" helpers, so a guard is not flagged as literally unused ---
// These never inspect the guards' (opaque) fields -- they exist only so
// that fixture functions have a reason to hold a guard past its creation
// point, which is what makes the drop-placement patterns below meaningful.

fn touch(_g: &Guard<'_>) {}
fn touch_read(_r: &ReadGuard<'_>) {}
fn touch_option(_o: &Option<Guard<'_>>) {}
fn do_other_work() {}
fn do_something() {}
/// Opaque-ish predicate over a guard, used only so `match_arm_with_guard_
/// clause` below has a reason to reference an already-bound guard from
/// inside a match arm's guard clause (rather than merely in its body).
fn guard_condition(_g: &Guard<'_>) -> bool {
    true
}

// ---------------------------------------------------------------------
// 1. Explicit `drop`
// ---------------------------------------------------------------------

/// EXPECTED: one acquire, released early via the explicit `drop(g)` call --
/// well before the end of the function -- rather than at the closing `}`.
#[verify::stateful_lifetimes]
pub fn explicit_drop(lock: &Lock) {
    let g = lock.acquire();
    touch(&g);
    drop(g);
    do_other_work();
}

// ---------------------------------------------------------------------
// 2. Nested scope
// ---------------------------------------------------------------------

/// EXPECTED: the guard is released at the closing `}` of the inner block,
/// strictly before `do_other_work` runs -- the inner block is its own drop
/// scope, nested inside (and ending before) the function's own scope.
#[verify::stateful_lifetimes]
pub fn nested_scope(lock: &Lock) {
    {
        let g = lock.acquire();
        touch(&g);
    }
    do_other_work();
}

// ---------------------------------------------------------------------
// 3. Implicit function scope
// ---------------------------------------------------------------------

/// EXPECTED: no explicit `drop` and no inner block -- the guard is released
/// implicitly at the function's closing `}`, i.e. after `do_other_work`.
#[verify::stateful_lifetimes]
pub fn implicit_function_scope(lock: &Lock) {
    let g = lock.acquire();
    touch(&g);
    do_other_work();
}

// ---------------------------------------------------------------------
// 4. `let _` (immediate drop, no binding at all)
// ---------------------------------------------------------------------

/// EXPECTED: `let _ = expr;` does **not** bind `expr`'s value to a name --
/// `_` is a wildcard pattern, not an identifier. The guard is therefore
/// released immediately, at the end of this `let` statement, exactly as if
/// it had been written as the bare expression statement `lock.acquire();`
/// (see `statement_end_drop` below). This is subtly different from
/// `let _guard = expr;`, which *does* bind a name (see next fixture).
#[verify::stateful_lifetimes]
pub fn let_underscore_immediate_drop(lock: &Lock) {
    let _ = lock.acquire();
    do_other_work();
}

// ---------------------------------------------------------------------
// 5. `let _guard` (named, underscore-prefixed -- held for the whole scope)
// ---------------------------------------------------------------------

/// EXPECTED: unlike `let _ = ...`, `let _guard = ...` binds a real name
/// (merely one that starts with `_`, which only suppresses the "unused
/// variable" lint -- it does not turn the pattern into a wildcard). The
/// guard is therefore held for the *entire* remaining function scope and
/// released only at the closing `}`, after `do_other_work`.
#[verify::stateful_lifetimes]
pub fn unused_named_guard(lock: &Lock) {
    let _guard = lock.acquire();
    do_other_work();
}

// ---------------------------------------------------------------------
// 6. Statement-end drop (bare expression statement)
// ---------------------------------------------------------------------

/// EXPECTED: `lock.acquire();` on its own creates a temporary `Guard` that
/// is never bound to anything, so it is released at the end of this
/// statement -- before `do_other_work` runs. Semantically identical to
/// `let_underscore_immediate_drop` above, just without the `let`.
#[verify::stateful_lifetimes]
pub fn statement_end_drop(lock: &Lock) {
    lock.acquire();
    do_other_work();
}

// ---------------------------------------------------------------------
// 7. Shadowing
// ---------------------------------------------------------------------

/// EXPECTED (the classic real-world "shadowed mutex guard" footgun):
/// shadowing a binding does **not** drop the shadowed value early. Both
/// guards are alive simultaneously from the second `let` until the end of
/// the function, where they are released in reverse declaration order:
/// the *second* `g` first, then the *first* `g`. A verifier that assumed
/// shadowing releases the old guard immediately would be unsound here --
/// with a real mutex this pattern can deadlock if the second `acquire`
/// targets the same lock reentrantly.
///
/// CURRENT (BUG): `simplify_duplicate_calls` merges the two identical
/// `lock.acquire()` calls in generated Lean, so today's baseline contains
/// only one guard. Keep this source shape: it is the regression test for
/// preserving both stateful acquires once calls become effect-aware.
#[verify::stateful_lifetimes]
pub fn shadowing_same_lock(lock: &Lock) {
    let g = lock.acquire();
    touch(&g);
    let g = lock.acquire();
    touch(&g);
}

// ---------------------------------------------------------------------
// 8. Mutable assignment overwrite
// ---------------------------------------------------------------------

/// EXPECTED: for a plain assignment `place = expr;`, Rust evaluates `expr`
/// **before** dropping the old value at `place` (see the Rust Reference's
/// "Assignment expressions" evaluation order). So the second
/// `lock.acquire()` happens *while the first guard is still held* -- both
/// are briefly alive at once -- and only afterwards is the first guard
/// dropped and replaced. The final guard is released at the end of the
/// function.
///
/// CURRENT (BUG): generated Lean merges the two identical acquires into
/// one through `simplify_duplicate_calls`.
#[verify::stateful_lifetimes]
pub fn assign_overwrite_same_lock(lock: &Lock) {
    let mut g = lock.acquire();
    touch(&g);
    g = lock.acquire();
    touch(&g);
}

/// Same rule as above, but across two different locks, to make the
/// "briefly both alive" window unambiguous: `lock_b.acquire()` runs while
/// `g` (still holding `lock_a`'s guard) has not yet been dropped.
#[verify::stateful_lifetimes]
pub fn assign_overwrite_different_locks<'a>(lock_a: &'a Lock, lock_b: &'a Lock) {
    let mut g = lock_a.acquire();
    touch(&g);
    g = lock_b.acquire();
    touch(&g);
}

// ---------------------------------------------------------------------
// 9. Tuple / struct destructuring
// ---------------------------------------------------------------------

/// EXPECTED: both guards are acquired to build the tuple (left-to-right:
/// `g1`'s acquire, then `g2`'s), then destructured into two bindings. Per
/// the drop order rule for multi-binding patterns, the bindings are
/// released in the reverse of the order they appear in the pattern: `g2`
/// first, then `g1`.
///
/// CURRENT (BUG): generated Lean merges both identical acquires.
#[verify::stateful_lifetimes]
pub fn destructure_tuple(lock: &Lock) {
    let (g1, g2) = (lock.acquire(), lock.acquire());
    touch(&g1);
    touch(&g2);
}

/// EXPECTED: same rule applied to a struct pattern -- `pair` is built with
/// `first` acquired before `second`; after destructuring into `first` and
/// `second` locals, they are released in reverse pattern order: `second`
/// first, then `first`.
///
/// CURRENT (BUG): generated Lean merges both identical acquires.
#[verify::stateful_lifetimes]
pub fn destructure_struct(lock: &Lock) {
    let pair = GuardPair {
        first: lock.acquire(),
        second: lock.acquire(),
    };
    let GuardPair { first, second } = pair;
    touch(&first);
    touch(&second);
}

// ---------------------------------------------------------------------
// 10. Nested guards with reverse drop order
// ---------------------------------------------------------------------

/// EXPECTED: two independent locks, acquired in order `lock_a` then
/// `lock_b`. Released in the exact reverse order at the end of the
/// function: `g2` (`lock_b`) first, then `g1` (`lock_a`).
#[verify::stateful_lifetimes]
pub fn nested_two_guards_reverse_order(lock_a: &Lock, lock_b: &Lock) {
    let g1 = lock_a.acquire();
    let g2 = lock_b.acquire();
    touch(&g1);
    touch(&g2);
}

/// EXPECTED: three independent locks, acquired `lock_a`, `lock_b`,
/// `lock_c` in order. Released in exact reverse order: `g3`, then `g2`,
/// then `g1`.
#[verify::stateful_lifetimes]
pub fn nested_three_guards_reverse_order(lock_a: &Lock, lock_b: &Lock, lock_c: &Lock) {
    let g1 = lock_a.acquire();
    let g2 = lock_b.acquire();
    let g3 = lock_c.acquire();
    touch(&g1);
    touch(&g2);
    touch(&g3);
}

// ---------------------------------------------------------------------
// 11. Conditional initialization
// ---------------------------------------------------------------------

/// EXPECTED: `g` is declared with no initializer and assigned exactly once,
/// along whichever branch runs (Rust's definite-assignment analysis
/// guarantees exactly one of the two assignments executes). Regardless of
/// which branch initializes it, there is exactly one acquire/release pair:
/// the acquire happens inside the taken branch, the release happens at the
/// function's closing `}`.
#[verify::stateful_lifetimes]
pub fn conditional_initialization(lock: &Lock, cond: bool) {
    let g;
    if cond {
        g = lock.acquire();
    } else {
        g = lock.acquire();
    }
    touch(&g);
}

/// EXPECTED: the guard is acquired only along the `cond` branch; when taken,
/// it is released at the closing `}` of the `if` block (a nested scope),
/// strictly before `do_other_work` -- on the `else` path, there is no
/// acquire/release pair at all.
#[verify::stateful_lifetimes]
pub fn conditional_guard_one_branch(lock: &Lock, cond: bool) {
    if cond {
        let g = lock.acquire();
        touch(&g);
    }
    do_other_work();
}

// ---------------------------------------------------------------------
// 12. Guard in `Option`
// ---------------------------------------------------------------------

/// EXPECTED: when `cond` is true, exactly one acquire happens, wrapped in
/// `Some`. The contained `Guard` (if any) is released precisely when
/// `maybe_guard` -- and thus the `Option` that owns it -- goes out of scope
/// at the end of the function; dropping an `Option<Guard>` drops its
/// contents only if it is `Some`.
#[verify::stateful_lifetimes]
pub fn guard_in_option(lock: &Lock, cond: bool) {
    let mut maybe_guard: Option<Guard<'_>> = None;
    if cond {
        maybe_guard = Some(lock.acquire());
    }
    touch_option(&maybe_guard);
}

// ---------------------------------------------------------------------
// 13. `take` / `replace`
// ---------------------------------------------------------------------

/// EXPECTED: one acquire (line 1). `Option::take` moves the guard out of
/// `maybe_guard` (which becomes `None`) into `taken`; the explicit
/// `drop(taken)` releases it immediately -- well before the end of the
/// function -- leaving `maybe_guard` empty (no release needed for it).
#[verify::stateful_lifetimes]
pub fn guard_take(lock: &Lock) {
    let mut maybe_guard = Some(lock.acquire());
    let taken = maybe_guard.take();
    drop(taken);
    do_other_work();
}

/// EXPECTED: two acquires -- one to build `maybe_guard`, one as the
/// argument to `replace` (per the "RHS evaluated first" rule from
/// `assign_overwrite_same_lock`, this second acquire happens before the old
/// value is displaced). `Option::replace` returns the *old* contents as
/// `old`, which is released immediately by `drop(old)`; the *new* guard,
/// now inside `maybe_guard`, is released at the end of the function.
///
/// CURRENT (BUG): generated Lean merges both identical acquires.
#[verify::stateful_lifetimes]
pub fn guard_replace(lock: &Lock) {
    let mut maybe_guard = Some(lock.acquire());
    let old = maybe_guard.replace(lock.acquire());
    drop(old);
    touch_option(&maybe_guard);
}

// ---------------------------------------------------------------------
// 14. `swap`
// ---------------------------------------------------------------------

/// EXPECTED: two independent acquires (`g1` from `lock_a`, `g2` from
/// `lock_b`). After `mem::swap`, `g1` holds what was originally `g2`'s
/// guard and vice versa -- but *which storage slot* is released first is
/// unaffected by the swap: slots still release in reverse declaration
/// order. So `g2`'s slot (now holding the `lock_a` guard) is released
/// first, then `g1`'s slot (now holding the `lock_b` guard).
#[verify::stateful_lifetimes]
pub fn guard_swap<'a>(lock_a: &'a Lock, lock_b: &'a Lock) {
    let mut g1 = lock_a.acquire();
    let mut g2 = lock_b.acquire();
    std::mem::swap(&mut g1, &mut g2);
    touch(&g1);
    touch(&g2);
}

// ---------------------------------------------------------------------
// 15. Guard moved between locals
// ---------------------------------------------------------------------

/// EXPECTED: a single acquire. Moving `g1` into `g2` transfers ownership of
/// the same guard value; `g1`'s binding is moved-from and therefore never
/// itself triggers a release. The value is released exactly once, when
/// `g2` goes out of scope at the end of the function.
#[verify::stateful_lifetimes]
pub fn guard_moved_between_locals(lock: &Lock) {
    let g1 = lock.acquire();
    let g2 = g1;
    touch(&g2);
}

// ---------------------------------------------------------------------
// 16. Block expression returns guard
// ---------------------------------------------------------------------

/// EXPECTED: the inner block's *tail expression* (no semicolon) is the
/// acquire itself, so `do_something()` runs first -- before any guard is
/// held -- and only then is the guard produced as the block's value and
/// bound to `g`. Crucially, `g`'s scope is the *outer* function, not the
/// inner block: the guard is released at the function's closing `}`, not
/// at the inner block's closing `}`.
#[verify::stateful_lifetimes]
pub fn block_expr_returns_guard(lock: &Lock) {
    let g = {
        do_something();
        lock.acquire()
    };
    touch(&g);
}

// ---------------------------------------------------------------------
// 17. Multiple read guards
// ---------------------------------------------------------------------

/// EXPECTED: three independent *shared* acquires (`RwLock::read`-style).
/// Because `read` only needs `&self`, all three coexist without conflict at
/// the type level; they release in reverse declaration order at the end of
/// the function: `r3`, then `r2`, then `r1`.
///
/// CURRENT (BUG): generated Lean merges all three identical reads into one.
#[verify::stateful_lifetimes]
pub fn multiple_read_guards(lock: &Lock) {
    let r1 = lock.read();
    let r2 = lock.read();
    let r3 = lock.read();
    touch_read(&r1);
    touch_read(&r2);
    touch_read(&r3);
}

/// EXPECTED: a shared guard `r` and an exclusive guard `w` on the *same*
/// lock, held simultaneously. CURRENT: our opaque `Lock` type does not
/// enforce real mutual exclusion at the type level (a real `RwLock` would
/// block or deadlock acquiring `w` while `r` is outstanding) -- that is a
/// *runtime* property of the real primitive, not something the borrow
/// checker (or this fixture) models. `w` releases first (reverse
/// declaration order), then `r`.
#[verify::stateful_lifetimes]
pub fn read_then_write_same_lock(lock: &Lock) {
    let r = lock.read();
    touch_read(&r);
    let w = lock.acquire();
    touch(&w);
}

// ---------------------------------------------------------------------
// 18. Partial move out of a named-field struct
// ---------------------------------------------------------------------

/// EXPECTED (verified with a `Drop`-instrumented reproduction under
/// `--edition 2021`): `pair.first` is moved out of the named binding
/// `pair` into `moved_first` -- a *partial move*. `GuardPair` itself has no
/// `Drop` impl (only its fields do), so this partial move is legal, and
/// `pair` remains usable for its still-owned `second` field afterwards.
/// Ordinary reverse-declaration-order governs release, treating
/// `moved_first` as if it were declared at the point of the partial move
/// (after `pair`): `moved_first` (the guard originally in `first`) is
/// released first, then `pair` (really, its one remaining field `second`)
/// is released at the function's closing `}`.
///
/// CURRENT (BUG): generated Lean merges both identical acquires.
#[verify::stateful_lifetimes]
pub fn partial_aggregate_move(lock: &Lock) {
    let pair = GuardPair {
        first: lock.acquire(),
        second: lock.acquire(),
    };
    let moved_first = pair.first;
    touch(&moved_first);
    touch(&pair.second);
}

// ---------------------------------------------------------------------
// 19. Partial move out of a tuple struct
// ---------------------------------------------------------------------

/// EXPECTED: identical rule to `partial_aggregate_move`, just with
/// positional (`.0` / `.1`) field access on a tuple struct instead of named
/// fields: `pair.0` is moved into `moved0`, `pair.1` remains in `pair`, and
/// `moved0` releases first, then `pair` (its remaining `.1` field) at the
/// function's closing `}`.
///
/// CURRENT (BUG): generated Lean merges both identical acquires.
#[verify::stateful_lifetimes]
pub fn tuple_struct_partial_move(lock: &Lock) {
    let pair = GuardTuplePair(lock.acquire(), lock.acquire());
    let moved0 = pair.0;
    touch(&moved0);
    touch(&pair.1);
}

// ---------------------------------------------------------------------
// 20. Destructuring assignment
// ---------------------------------------------------------------------

/// EXPECTED (verified empirically -- destructuring *assignment*, `(a, b) =
/// (..);`, stable since Rust 1.59, is distinct from a destructuring `let`):
/// per the same "RHS evaluated before the old value is dropped" rule as
/// `assign_overwrite_same_lock`, both elements of the RHS tuple are
/// acquired first (left to right: the value for `a`, then the value for
/// `b`), and only afterwards are the *old* contents of `a` and `b` dropped
/// -- in left-to-right pattern order (`a`'s old guard first, then `b`'s).
/// The two new guards, now held in `a` and `b`, are released at the
/// function's closing `}` in the usual reverse-declaration order: `b`
/// first, then `a`.
///
/// CURRENT (BUG): generated Lean merges all four identical acquires into
/// one, making this a direct multiplicity regression fixture.
#[verify::stateful_lifetimes]
pub fn destructuring_assignment(lock: &Lock) {
    let mut a = lock.acquire();
    let mut b = lock.acquire();
    touch(&a);
    touch(&b);
    (a, b) = (lock.acquire(), lock.acquire());
    touch(&a);
    touch(&b);
}

// ---------------------------------------------------------------------
// 21. Struct pattern with fields listed out of declaration order
// ---------------------------------------------------------------------

/// EXPECTED (verified empirically, and contrasted with `destructure_struct`
/// above): the drop-order rule for a multi-binding pattern is "reverse of
/// the order the *bindings* appear in the pattern", not the struct's field
/// *declaration* order. `destructure_struct` writes its pattern as
/// `{ first, second }` (declaration order), giving reversed release order
/// `second`, then `first`. Here the pattern is written **reversed**,
/// `{ second, first }` -- so the appearance order is `[second, first]`,
/// its reverse is `[first, second]`, and `first` is released *before*
/// `second` this time: the exact opposite of `destructure_struct`, even
/// though both destructure the very same `GuardPair` layout.
///
/// CURRENT (BUG): generated Lean merges both identical acquires.
#[verify::stateful_lifetimes]
pub fn destructure_struct_reversed_pattern(lock: &Lock) {
    let pair = GuardPair {
        first: lock.acquire(),
        second: lock.acquire(),
    };
    let GuardPair { second, first } = pair;
    touch(&first);
    touch(&second);
}

// ---------------------------------------------------------------------
// 22. `let ... else`
// ---------------------------------------------------------------------

/// EXPECTED (verified empirically; `let-else`, stable since Rust 1.65): on
/// the success path, `g` is a genuine `let`-bound local -- unlike an
/// `if let`'s consequent-scoped binding (see `if_let_some_temporary` in
/// `lt-stateful-temporaries.rs`), a `let ... else` binding's scope is the
/// **entire rest of the enclosing block**, exactly as if it had been an
/// ordinary `let`. So `g` survives past `do_something()` and is released
/// only at the function's closing `}`. On the failure path, the `else`
/// block is a diverging scope (must return `!`, e.g. via `return`): no
/// guard is ever acquired at all, since the condition's scrutinee
/// evaluated to `None`.
#[verify::stateful_lifetimes]
pub fn let_else_binding(lock: &Lock, cond: bool) {
    let Some(g) = (if cond { Some(lock.acquire()) } else { None }) else {
        do_other_work();
        return;
    };
    touch(&g);
    do_something();
}

// ---------------------------------------------------------------------
// 23. `match` arm with a guard clause referencing an existing binding
// ---------------------------------------------------------------------

/// EXPECTED: `g` is an ordinary named binding, acquired *before* the
/// `match` (unlike `lt-stateful-temporaries.rs`'s "temporary in a match
/// guard" fixture, where the temporary is created fresh *inside* the guard
/// condition itself). Referencing `g` from a guard clause (`if
/// guard_condition(&g)`) does not move it, borrow it for longer than the
/// guard's own evaluation, or otherwise change its scope in any way --
/// `g` is released at the function's closing `}`, exactly as in
/// `implicit_function_scope`, regardless of which arm's guard clause(s)
/// ran or which arm was taken.
#[verify::stateful_lifetimes]
pub fn match_arm_with_guard_clause(lock: &Lock, cond: bool) {
    let g = lock.acquire();
    match cond {
        true if guard_condition(&g) => touch(&g),
        _ => touch(&g),
    }
    do_other_work();
}

// ---------------------------------------------------------------------
// 24. Nested closure capture
// ---------------------------------------------------------------------

/// EXPECTED (verified empirically): `move || { touch(&g); true }` captures `g`
/// *by value* into the closure's environment, so `g` is no longer an
/// independent local of this function -- it effectively becomes a field of
/// the value bound to `holder`. Calling `holder()` runs the closure body
/// (which only borrows its captured `g` via `touch(&g)`) without consuming
/// the closure itself, so `holder` -- and the `g` living inside it -- stays
/// alive across the call. The guard is released only when `holder` itself
/// is dropped, at this function's closing `}`, strictly after
/// `do_other_work()` -- **not** when the closure body finishes executing.
///
/// NOTE: the boolean sentinel avoids a current generated-Lean mismatch in
/// the synthesized `FnMut` support for a unit-returning captured closure
/// (`call_mut` otherwise loses the
/// unit output). It does not change the guard's capture or drop scope.
#[verify::stateful_lifetimes]
pub fn nested_closure_capture(lock: &Lock) {
    let g = lock.acquire();
    let holder = move || {
        touch(&g);
        true
    };
    let _touched = holder();
    do_other_work();
}

// ---------------------------------------------------------------------
// 25. Aggregate and intentional-leak edge cases
// ---------------------------------------------------------------------

/// EXPECTED: an aggregate that is never destructured drops its fields in
/// declaration order, not reverse local-binding order: `first`, then
/// `second`.
#[verify::stateful_lifetimes]
pub fn aggregate_fields_drop_in_declaration_order(lock_a: &Lock, lock_b: &Lock) {
    let pair = GuardPair {
        first: lock_a.acquire(),
        second: lock_b.acquire(),
    };
    touch(&pair.first);
    touch(&pair.second);
}

/// EXPECTED: array elements are dropped in increasing index order.
#[verify::stateful_lifetimes]
pub fn array_elements_drop_in_index_order(lock_a: &Lock, lock_b: &Lock, lock_c: &Lock) {
    let guards = [lock_a.acquire(), lock_b.acquire(), lock_c.acquire()];
    touch(&guards[0]);
    touch(&guards[1]);
    touch(&guards[2]);
}

/// EXPECTED: `mem::forget` intentionally leaks the guard, so there is one
/// acquire and no matching release event.
#[verify::stateful_lifetimes]
pub fn forgotten_guard_has_no_release(lock: &Lock) {
    let g = lock.acquire();
    std::mem::forget(g);
    do_other_work();
}

// ---------------------------------------------------------------------
// Unsupported patterns (documented as comments, not compiled code)
// ---------------------------------------------------------------------
//
// UNSUPPORTED (self-referential struct): a struct cannot hold both the
// `Lock` it owns and a `Guard` borrowing from that same field -- Rust has
// no direct support for self-referential structs (that requires either
// unsafe code or an external crate such as `ouroboros`). The following
// sketch would fail to compile with a lifetime error ("borrowed value does
// not live long enough" / cannot name the field's own lifetime), so it is
// left here only as an explanatory comment:
//
// struct SelfRefHolder {
//     lock: Lock,
//     guard: Guard<'this_cannot_name_the_field_above>,
// }
//
// UNSUPPORTED (returning a guard that outlives its lock parameter): a
// function cannot return a `Guard<'a>` derived from a `Lock` it created
// locally, since the local `Lock` would be dropped at the end of the
// function while the `Guard` (which borrows it) escapes:
//
// fn make_and_acquire() -> Guard<'static> {
//     let local_lock = Lock;       // dropped at the end of this function
//     local_lock.acquire()         // ERROR: `local_lock` does not live
//                                  // long enough to satisfy `'static`
// }
