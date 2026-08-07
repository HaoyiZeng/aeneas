//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]

//! Fixtures for **temporary** value drop-timing rules, applied to opaque
//! stateful guards (think `MutexGuard`, `RwLockReadGuard`, ...).
//!
//! This file complements `lt-stateful-drop.rs`: that file covers *named
//! bindings* and structural scoping (explicit `drop`, nested blocks,
//! shadowing, `Option`, `take`/`replace`, ...), while this file focuses on
//! *unnamed temporaries* -- values produced by an expression that is never
//! bound to a `let` at all (or only indirectly, through a reference) -- and
//! the specific, sometimes surprising, rules that govern how long they live.
//!
//! ## Sources
//!
//! Every claim below is checked against the Rust Reference, and against the
//! **Rust 2021** edition specifically -- these fixtures are compiled with
//! `--edition=2021` (see `tests/test_runner/run_test.ml`), which predates the
//! 2024-edition "if-let rescoping" change to `if let` temporary scopes (see
//! `if_let_else_temporary` below for the one fixture where the two editions
//! disagree):
//! - "Destructors" -> "Temporary scopes"
//!   (<https://doc.rust-lang.org/reference/destructors.html#temporary-scopes>)
//! - "Destructors" -> "Temporary lifetime extension"
//!   (<https://doc.rust-lang.org/reference/destructors.html#temporary-lifetime-extension>)
//! - "Loop expressions" -> "Iterator loops"
//!   (<https://doc.rust-lang.org/reference/expressions/loop-expr.html#iterator-loops>)
//! - Edition Guide -> "Rust 2024" -> "if let temporary scope"
//!   (<https://doc.rust-lang.org/edition-guide/rust-2024/temporary-if-let-scope.html>)
//!
//! CURRENT BASELINE:
//! As in `lt-stateful-drop.rs`, `#[verify::stateful_lifetimes]` is a
//! **tentative** marker attribute: registered via `#![register_tool(verify)]`
//! so `rustc` accepts it, but not one of the names Charon's
//! `parse_special_attr` recognizes (unlike `#[verify::opaque]` and
//! `#[verify::test]`, which it special-cases and accepts silently). Today
//! this makes Charon emit an `Unrecognized attribute` warning
//! (`Level::WARNING`, via `register_error!`) for every fixture in this file,
//! not silence -- identifying, in the meantime, which functions are meant as
//! fixtures for a not-yet-existing verification pass.
//!
//! One fixture -- the "for loop head expression" guard footgun, which needs
//! a genuinely non-opaque method borrowing through an opaque struct's field
//! -- currently crashes Aeneas's translation (`Can't retrieve the variants
//! of non-adt type: Guard`) rather than producing a clean baseline. It is
//! isolated in `lt-stateful-drop-known-failures.rs` (alongside its own
//! minimal opaque prelude) so that the rest of this suite can keep
//! generating successfully; see that file's module doc for the repro and
//! root-cause explanation.
//!
//! As in the companion drop suite, every release point below is
//! **aspirational under the current baseline**. Aeneas presently emits no
//! implicit end-of-scope `Drop::drop` call, so the generated Lean preserves
//! temporary/acquire data flow but not the destructor event itself.

// ---------------------------------------------------------------------
// Opaque Lock / Guard prelude
// ---------------------------------------------------------------------

/// An opaque handle to an external synchronization primitive. As in
/// `lt-stateful-drop.rs`, no `Lock` is ever constructed in this file --
/// every fixture receives one as a parameter, since these fixtures are
/// never executed (only ever type/borrow-checked).
#[verify::opaque]
pub struct Lock;

/// An opaque RAII guard representing exclusive ownership of a `Lock`.
#[verify::opaque]
pub struct Guard<'a> {
    lock: &'a Lock,
}

impl Lock {
    /// EXPECTED: an "acquire" event for `self`; the matching "release" event
    /// happens exactly when the returned `Guard` is dropped.
    #[verify::opaque]
    pub fn acquire(&self) -> Guard<'_> {
        unimplemented!()
    }

    /// Fallible acquire, used only so `while_let_temporary` below has a
    /// `while let` scrutinee that plausibly terminates (an infallible
    /// `acquire` would give no reason for the loop to ever stop).
    #[verify::opaque]
    pub fn try_acquire(&self) -> Option<Guard<'_>> {
        unimplemented!()
    }
}

impl<'a> Guard<'a> {
    /// Opaque predicate, used only so fixtures below have a reason to call a
    /// method *on* a guard temporary (rather than merely constructing one).
    #[verify::opaque]
    pub fn is_valid(&self) -> bool {
        unimplemented!()
    }

    /// Opaque predicate over *two* guards, used only so
    /// `receiver_and_arg_temporaries` below has a reason to make a single
    /// call whose receiver **and** argument are each their own temporary.
    #[verify::opaque]
    pub fn is_valid_with(&self, _other: &Guard<'_>) -> bool {
        unimplemented!()
    }
}

/// The `drop` method itself must be `#[verify::opaque]`:
/// `Guard` is an opaque struct, so Aeneas has no visibility into its
/// (private) `lock` field, and a transparent `drop` body cannot access it
/// (this is the same convention used by `AutoGuard`/`Arc` in
/// `lt-stateful-passes.rs` and `lt-stateful-arc.rs`, and by `Guard`'s own
/// `impl Drop` in `lt-stateful-drop.rs`).
impl<'a> Drop for Guard<'a> {
    #[verify::opaque]
    fn drop(&mut self) {
        unimplemented!()
    }
}

// --- small "use" helpers ---

fn touch(_g: &Guard<'_>) {}
fn touch_bool(_b: bool) {}
fn touch_item(_x: u32) {}
fn do_other_work() {}
fn do_something() {}
/// Consumes a guard *by value*, used only to contrast by-value callee
/// ownership (`call_arg_by_value_ownership` below) with the by-reference
/// argument passing of `call_arg_temporary` above.
fn touch_owned(_g: Guard<'_>) {}
/// Opaque predicate over two by-reference guards, used only so
/// `two_by_ref_arg_temporaries` below has a reason to pass two independent
/// guard temporaries as arguments to a single call.
#[verify::opaque]
fn combine(_a: &Guard<'_>, _b: &Guard<'_>) -> bool {
    unimplemented!()
}

// ---------------------------------------------------------------------
// 1. Function-call argument temporary
// ---------------------------------------------------------------------

/// EXPECTED: per the Reference's own counter-example ("The borrows in `&0 +
/// &1` and `f(&mut 0)` are not [extending]"), passing a temporary directly
/// as a function argument does **not** extend its lifetime. `lock.acquire()`
/// creates a `Guard` temporary borrowed for the duration of the `touch`
/// call; it is released at the end of this statement, right after `touch`
/// returns.
#[verify::stateful_lifetimes]
pub fn call_arg_temporary(lock: &Lock) {
    touch(&lock.acquire());
    do_other_work();
}

// ---------------------------------------------------------------------
// 2. Chained method call temporary
// ---------------------------------------------------------------------

/// EXPECTED: `lock.acquire()` produces a `Guard` temporary that is the
/// receiver of `.is_valid()`. The temporary is released once the whole
/// statement (here, the function's tail expression) finishes evaluating --
/// i.e. after `is_valid` returns its `bool`, but before that `bool` is
/// handed back to the caller.
#[verify::stateful_lifetimes]
pub fn chained_call_temporary(lock: &Lock) -> bool {
    lock.acquire().is_valid()
}

// ---------------------------------------------------------------------
// 3. Temporary in a `return` expression
// ---------------------------------------------------------------------

/// EXPECTED: same rule as `chained_call_temporary`, just with an explicit
/// `return`. The guard temporary is released at the end of this `return`
/// statement -- immediately before the function actually returns to its
/// caller.
#[verify::stateful_lifetimes]
pub fn temporary_in_return_position(lock: &Lock) -> bool {
    return lock.acquire().is_valid();
}

// ---------------------------------------------------------------------
// 4. `if` condition temporary
// ---------------------------------------------------------------------

/// EXPECTED: the Reference lists "the non-pattern-matching condition
/// expression of an `if` ... expression" as its own temporary scope. So the
/// guard temporary created while evaluating the condition is released
/// **once the condition has been evaluated to a `bool`**, strictly before
/// either branch's body runs.
#[verify::stateful_lifetimes]
pub fn if_condition_temporary(lock: &Lock) {
    if lock.acquire().is_valid() {
        do_something();
    } else {
        do_other_work();
    }
}

// ---------------------------------------------------------------------
// 5. `while` condition temporary
// ---------------------------------------------------------------------

/// EXPECTED: same rule as `if_condition_temporary`, applied every
/// iteration: a *fresh* guard is acquired and released each time the
/// condition is (re-)evaluated, before the loop body (if any) runs for that
/// iteration.
#[verify::stateful_lifetimes]
pub fn while_condition_temporary(lock: &Lock, mut n: u32) {
    while lock.acquire().is_valid() && n > 0 {
        n -= 1;
    }
}

// ---------------------------------------------------------------------
// 6. Compound / lazy-boolean operand temporaries
// ---------------------------------------------------------------------

/// EXPECTED: the Reference lists "each operand of a lazy boolean
/// expression" as its own temporary scope, with an explicit example
/// ("Dropped before the first `||`", "Dropped before the `)`", ...). So each
/// `acquire()` here is released immediately after *its own* `is_valid()`
/// check, before the next operand is even evaluated -- not held until the
/// end of the whole `&&` expression. Because `&&` short-circuits, if
/// `lock_a`'s guard is invalid, `lock_b.acquire()` never runs at all (no
/// second acquire happens).
#[verify::stateful_lifetimes]
pub fn compound_expression_temporaries(lock_a: &Lock, lock_b: &Lock) {
    let ok = lock_a.acquire().is_valid() && lock_b.acquire().is_valid();
    touch_bool(ok);
}

// ---------------------------------------------------------------------
// 7. Match arm binds (moves) the scrutinee temporary
// ---------------------------------------------------------------------

/// EXPECTED: `g` (a plain catch-all identifier pattern) moves the guard out
/// of the scrutinee temporary into a genuine local variable. Per
/// "Local variables declared in a match expression ... are associated to
/// the arm scope", `g` is released at the closing `}` of its arm -- here,
/// effectively at the end of the `match` statement.
#[verify::stateful_lifetimes]
pub fn match_arm_move_binding_temporary(lock: &Lock) {
    match lock.acquire() {
        g => touch(&g),
    }
}

// ---------------------------------------------------------------------
// 8. "Match temporary": the scrutinee is *not* a temporary scope
// ---------------------------------------------------------------------

/// EXPECTED (mirrors the Rust Reference's own illustrative example,
/// `match 1 { ref mut z => z };`, translated to our `Guard` type): the
/// Reference states explicitly, "the scrutinee of a match expression is not
/// a temporary scope, so temporaries in the scrutinee can be dropped after
/// the match expression". Using `ref r` borrows the scrutinee's `Guard`
/// temporary instead of moving it into a local, so the temporary is not
/// consumed by the arm. Its scope bubbles up past the (non-scope-forming)
/// match to the nearest enclosing temporary scope -- here, this whole
/// statement -- so it survives exactly long enough for the match to finish
/// evaluating to `r`, which is then discarded.
#[verify::stateful_lifetimes]
pub fn match_scrutinee_is_not_a_temporary_scope(lock: &Lock) {
    match lock.acquire() {
        ref r => r,
    };
}

// ---------------------------------------------------------------------
// 9. `if let` binding moves the scrutinee's contents
// ---------------------------------------------------------------------

/// EXPECTED: `Some(lock.acquire())` is matched against `Some(g)`, which
/// *moves* the guard out of the temporary `Option` and into the named
/// binding `g`. Since `if let` desugars to `match`, the same binding rule
/// as `match_arm_move_binding_temporary` applies: `g` is released at the
/// closing `}` of the consequent block, well before any code that might
/// follow this `if let`.
#[verify::stateful_lifetimes]
pub fn if_let_some_temporary(lock: &Lock) {
    if let Some(g) = Some(lock.acquire()) {
        touch(&g);
    }
}

// ---------------------------------------------------------------------
// 10. `if let` / `else`: pattern-matching condition temporary
// ---------------------------------------------------------------------

/// EXPECTED (Rust 2021, the edition these fixtures are compiled under --
/// see `--edition=2021` in `tests/test_runner/run_test.ml`): here `true`
/// binds nothing, so (unlike the previous fixture) there is no named local
/// to reason about -- the guard produced by `lock.acquire()` is a genuine
/// leftover *temporary* of the condition expression. Before the 2024-edition
/// "if-let rescoping" change (`if_let_rescope`, tracked in
/// <https://github.com/rust-lang/rust/issues/124085>), the scrutinee of an
/// `if let ... else ...` is **not** its own temporary scope: it shares the
/// temporary scope of the whole `if let` statement, which encloses *both*
/// branches. So the guard temporary is held across the entire
/// `if let { .. } else { .. }` -- including the full `else` block -- and is
/// only released once the statement as a whole finishes evaluating, after
/// the taken branch body and before control continues past the statement.
///
/// This is exactly the footgun the 2024 edition fixes: since Rust 2024, the
/// scrutinee's temporary scope ends **before** the `else` block runs --
/// whether because the match succeeded (consequent already finished) or
/// failed (the scrutinee is dropped right before entering `else`) -- so
/// code that needs to re-acquire the same lock inside `else` no longer
/// deadlocks. Under the 2021 semantics verified here, attempting to
/// `lock.acquire()` again inside the `else` branch would still see the
/// first guard alive and could deadlock on a non-reentrant lock. Verified
/// empirically against both `--edition 2021` and `--edition 2024` with a
/// `Drop`-instrumented guard: only the 2024 build prints the drop before
/// entering the `else` arm.
#[verify::stateful_lifetimes]
pub fn if_let_else_temporary(lock: &Lock) {
    if let true = lock.acquire().is_valid() {
        do_something();
    } else {
        do_other_work();
    }
}

// ---------------------------------------------------------------------
// 11. `for` loop head expression temporary (the classic guard footgun)
// ---------------------------------------------------------------------

/// NOTE: the head-expression variant of this fixture (`for_loop_head_
/// temporary`, the "classic guard footgun" where the temporary is hoisted
/// once for the *entire* loop, via a receiver method that borrows through
/// an opaque struct's field) is isolated in
/// `lt-stateful-drop-known-failures.rs` -- it requires a non-opaque method
/// on an otherwise-`#[verify::opaque]` struct to genuinely borrow a private
/// field (so that its returned iterator borrows `self`), which currently
/// triggers a baseline Aeneas crash ("Can't retrieve the variants of
/// non-adt type: Guard") rather than a clean translation. See that file's
/// module doc for the full repro and root-cause explanation.
///
/// This fixture only covers the *contrasting* per-iteration-acquire shape:
/// the guard is acquired *inside* the loop body (not in the head/iterator
/// expression), so a fresh guard is acquired and released on every single
/// iteration -- never held across iterations.
#[verify::stateful_lifetimes]
pub fn for_loop_body_guard_per_iteration(lock: &Lock, n: u32) {
    for i in 0..n {
        let g = lock.acquire();
        touch(&g);
        touch_item(i);
    }
}

// ---------------------------------------------------------------------
// 12. Temporary lifetime extension via direct borrow
// ---------------------------------------------------------------------

/// EXPECTED: per "Extending based on expressions", the initializer
/// expression of a `let` statement is always an extending-expression
/// candidate, and "the operand of an extending borrow expression has its
/// temporary scope extended". Here the initializer *is* a borrow expression
/// (`&lock.acquire()`), so its operand's (the `Guard`'s) temporary scope is
/// extended to the enclosing block -- i.e. to the end of this function --
/// instead of being dropped at the end of this statement. This mirrors the
/// Reference's own canonical example, `let x = &mut 0;`.
#[verify::stateful_lifetimes]
pub fn temporary_lifetime_extension(lock: &Lock) {
    let g_ref: &Guard<'_> = &lock.acquire();
    touch(g_ref);
}

/// EXPECTED: extension also recurses through specific wrapping expression
/// forms -- the Reference's own example is `Some(&mut 3)`, "argument to
/// [an extending] tuple enum variant constructor". Here, `Some(&lock.acquire())`
/// is such a constructor call, so it is itself extending, and the borrow
/// inside it extends the `Guard` temporary's scope to the end of this
/// function (not just to the end of this statement).
#[verify::stateful_lifetimes]
pub fn temporary_lifetime_extension_through_option(lock: &Lock) {
    let wrapped: Option<&Guard<'_>> = Some(&lock.acquire());
    if let Some(g_ref) = wrapped {
        touch(g_ref);
    }
}

// ---------------------------------------------------------------------
// 13. Wildcard binding: plain value vs. extending borrow
// ---------------------------------------------------------------------

/// EXPECTED: `_` is a wildcard pattern, not a binding, so `let _ = expr;`
/// behaves exactly like the bare expression statement `expr;` -- the guard
/// temporary is released at the end of this statement. This is the
/// "temporaries" counterpart to `let_underscore_immediate_drop` in
/// `lt-stateful-drop.rs` (which frames the same rule from the
/// named-binding side, contrasting it with `let _guard = ...`).
#[verify::stateful_lifetimes]
pub fn let_underscore_is_a_plain_temporary(lock: &Lock) {
    let _ = lock.acquire();
    do_other_work();
}

/// EXPECTED: unlike the plain-value form above, the initializer here is an
/// extending borrow expression. Temporary lifetime extension therefore
/// keeps the acquired guard alive to the end of the enclosing block even
/// though the pattern itself is `_`.
#[verify::stateful_lifetimes]
pub fn let_underscore_extending_borrow(lock: &Lock) {
    let _ = &lock.acquire();
    do_other_work();
}

// ---------------------------------------------------------------------
// 14. By-value callee ownership (contrast with argument temporaries)
// ---------------------------------------------------------------------

/// EXPECTED (verified with a `Drop`-instrumented reproduction under
/// `--edition 2021`; contrast with `call_arg_temporary` above): passing
/// the guard **by value** moves it into `touch_owned`'s parameter, which
/// becomes its sole owner. The guard is therefore released *inside*
/// `touch_owned`, at the end of *its* body -- strictly before control
/// returns here -- rather than at the end of this statement in the
/// caller, as it would be for a by-reference argument.
#[verify::stateful_lifetimes]
pub fn call_arg_by_value_ownership(lock: &Lock) {
    touch_owned(lock.acquire());
    do_other_work();
}

// ---------------------------------------------------------------------
// 15. Two by-reference argument temporaries, with trailing code
// ---------------------------------------------------------------------

/// EXPECTED (verified empirically): both by-reference arguments are
/// acquired left to right (`lock_a`'s guard, then `lock_b`'s), and -- per
/// the Reference's rule that all temporaries produced while evaluating a
/// statement are released at the end of that statement, in reverse
/// creation order -- are released `lock_b`'s guard first, then `lock_a`'s,
/// strictly before `do_other_work` runs on the next statement.
#[verify::stateful_lifetimes]
pub fn two_by_ref_arg_temporaries(lock_a: &Lock, lock_b: &Lock) {
    combine(&lock_a.acquire(), &lock_b.acquire());
    do_other_work();
}

// ---------------------------------------------------------------------
// 16. Chained receiver temporary, with trailing code
// ---------------------------------------------------------------------

/// EXPECTED (verified empirically; extends `chained_call_temporary` above
/// with an explicit trailing statement to make the release point
/// unambiguous, rather than leaving it as this function's tail
/// expression): the receiver temporary is released at the end of *this*
/// statement -- strictly before `do_other_work` runs on the next one.
#[verify::stateful_lifetimes]
pub fn chained_receiver_with_trailing_code(lock: &Lock) {
    lock.acquire().is_valid();
    do_other_work();
}

// ---------------------------------------------------------------------
// 17. Receiver and argument temporaries in a single call
// ---------------------------------------------------------------------

/// EXPECTED (verified empirically): for a method call `receiver.method
/// (arg)`, the receiver expression is evaluated before the argument
/// expressions, so `lock_a.acquire()` (the receiver) is acquired first,
/// then `lock_b.acquire()` (the argument). Both are temporaries of the
/// same statement, so -- exactly as in `two_by_ref_arg_temporaries` --
/// they release together at the end of the statement, in reverse creation
/// order: the argument's guard first, then the receiver's.
#[verify::stateful_lifetimes]
pub fn receiver_and_arg_temporaries(lock_a: &Lock, lock_b: &Lock) {
    lock_a.acquire().is_valid_with(&lock_b.acquire());
    do_other_work();
}

// ---------------------------------------------------------------------
// 18. Temporary field projection out of a temporary tuple
// ---------------------------------------------------------------------

/// EXPECTED (verified empirically): `(lock.acquire().is_valid(), 0).0`
/// builds a temporary tuple and immediately projects its first field.
/// Unlike the extending forms in `temporary_lifetime_extension` /
/// `temporary_lifetime_extension_through_option` above (a direct borrow,
/// or a borrow inside an extending tuple-enum-variant constructor), a
/// field projection (`.0`) is *not* one of the specific forms the
/// Reference lists as extending -- so no extension happens here, even
/// though the projection is itself the initializer of a `let`. The whole
/// tuple temporary (and the `Guard` it was built from) is released at the
/// end of this `let` statement, immediately -- not extended to the end of
/// the enclosing function.
#[verify::stateful_lifetimes]
pub fn tuple_temporary_field_projection(lock: &Lock) -> bool {
    let ok = (lock.acquire().is_valid(), 0u32).0;
    do_other_work();
    ok
}

// ---------------------------------------------------------------------
// 19. Returning a guard wrapped in `Some` (ownership escapes via `return`)
// ---------------------------------------------------------------------

/// EXPECTED (verified empirically; contrast with `temporary_in_return_
/// position` above, where only a derived `bool` escapes and the guard is
/// released *inside* the function): here the guard itself, not a value
/// derived from it, is the thing being returned -- `Some(lock.acquire())`
/// moves the freshly acquired guard into the `Option` that becomes this
/// function's return value. No release happens inside this function at
/// all; ownership transfers to the caller, who now controls exactly when
/// the guard is released (by whatever `Drop`-scope rule governs wherever
/// the caller stores the returned `Option`).
#[verify::stateful_lifetimes]
pub fn return_some_temporary(lock: &Lock) -> Option<Guard<'_>> {
    Some(lock.acquire())
}

// ---------------------------------------------------------------------
// 20. `while let` condition temporary (fresh guard every iteration)
// ---------------------------------------------------------------------

/// EXPECTED (verified empirically; contrast with `for_loop_head_temporary`
/// in `lt-stateful-drop-known-failures.rs`, the "classic guard footgun"
/// where the temporary is hoisted once for the *entire* loop):
/// `while let PAT = scrutinee_expr { body }` re-evaluates `scrutinee_expr`
/// at the start of *every* iteration, so a fresh guard is acquired each
/// time the condition is checked. The bound value is scoped to that single
/// iteration's body (mirroring `if let`'s consequent-only binding scope)
/// and is released at the end of that iteration's body -- before the
/// condition is re-evaluated for the next iteration. Unlike
/// `for_loop_head_temporary`, no guard is ever held across more than one
/// iteration.
#[verify::stateful_lifetimes]
pub fn while_let_temporary(lock: &Lock) {
    while let Some(g) = lock.try_acquire() {
        touch(&g);
    }
}

// ---------------------------------------------------------------------
// 21. Temporary created inside a `match` guard clause
// ---------------------------------------------------------------------

/// EXPECTED (verified empirically; contrast with `lt-stateful-drop.rs`'s
/// "match arm with a guard clause referencing an existing binding" fixture,
/// where the guard clause merely *reads* an already-bound guard): here
/// `lock.acquire()` is created fresh, entirely *inside* the guard-clause
/// condition itself, with no named binding at all. The guard condition is
/// its own temporary scope (same rule as `if_condition_temporary` /
/// `while_condition_temporary` above), so this temporary is released
/// immediately after the guard finishes evaluating to a `bool` -- strictly
/// before the corresponding arm's body runs, regardless of which arm ends
/// up matching.
#[verify::stateful_lifetimes]
pub fn temporary_in_match_guard(lock: &Lock, selector: i32) {
    match selector {
        _ if lock.acquire().is_valid() => {
            do_something();
        }
        _ => {
            do_other_work();
        }
    }
}

// ---------------------------------------------------------------------
// Unsupported / out-of-scope patterns (documented as comments only)
// ---------------------------------------------------------------------
//
// UNSUPPORTED (returning a reference to a temporary without extension): if
// a function tried to return `&Guard` borrowed from
// inside it without one of the specific extending forms above, it would
// fail to compile ("temporary value dropped while borrowed" /
// "cannot return value referencing temporary value"). For example:
//
// fn dangling(lock: &Lock) -> &Guard<'_> {
//     let owned = lock.acquire();
//     &owned // ERROR: `owned` does not live long enough once we try to
//            // return a reference into it -- it is dropped at the end of
//            // this function, before the reference could be used by the
//            // caller.
// }
//
// This is not really about temporary lifetime extension (`owned` here is a
// named local, not a temporary) -- it is included as a reminder that
// extension only postpones *temporary* drops within the current function;
// it can never make a value outlive the function that created it.
