//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
#![allow(dead_code, unused_variables, unused_mut)]
//! # Stateful / Effectful Micro-Pass Regression Suite
//!
//! This file is a dense collection of small Rust functions that stress the
//! Aeneas optimizer / micro-pass pipeline (CSE, DCE, beta-reduction, branch
//! hoisting, tuple/projection rewriting, coalescing) in the presence of
//! **effectful** opaque calls and **effectful backward functions**
//! (Aeneas' term for the continuation generated when a Rust function returns
//! a mutable borrow, `&mut T`). Every micro-pass in this pipeline was
//! originally designed under the assumption that pure LLBC values could be
//! freely duplicated, merged, reordered, or dropped. Once a call (forward)
//! or a backward continuation is *effectful* — i.e. it corresponds to an
//! opaque, external, or otherwise untranslated piece of code that may have
//! side effects invisible to the analyzer (locking, reference counting,
//! logging, I/O) — those transformations are only sound if they preserve:
//!
//!  1. **Occurrence count**: the number of times each opaque call site is
//!     actually invoked at runtime must not change.
//!  2. **Relative order**: the program order between any two effectful
//!     calls (forward or backward) must be preserved exactly as written.
//!  3. **Conditionality**: an effectful call reachable only via a branch
//!     must not become unconditional (hoisting), and vice versa.
//!
//! ## EXPECTED
//! For every function below, the generated Lean translation must contain
//! exactly the opaque call sites named in that function's `EXPECTED` doc
//! comment, in the stated order, with the stated multiplicity — regardless
//! of the fact that many of these calls are syntactically identical
//! (same callee, same-looking arguments) and would be legal to
//! merge/eliminate/reorder if they were pure.
//!
//! ## CURRENT — this is not a hypothetical risk, it is a live bug
//! `src/pure/PureMicroPassesGeneral.ml`'s `simplify_duplicate_calls` pass
//! (registered in the pipeline as `"simplify_duplicate_calls"` in
//! `src/pure/PureMicroPasses.ml`) already runs today, unconditionally, on
//! every function. It caches each monadic `let`-bound call expression in a
//! structural `TExprMap` and rewrites any later, syntactically-identical
//! call to a reference to the first one's result — **with no effect
//! analysis at all**. Its own doc comment says as much:
//! > "TODO: this micro-pass will not be sound anymore once we allow
//! > stateful (backward) functions."
//! That future is now: this file's opaque calls are exactly those
//! "stateful (backward) functions". Functions below whose doc comment is
//! tagged `CURRENT (BUG):` are **known, currently-reproducing**
//! manifestations of this pass eliminating a real opaque call site — not
//! merely a guard against a not-yet-written future pass. They are kept in
//! this (non-`known-failure`) file because Aeneas does not error out on
//! them: translation *succeeds* and silently emits wrong (under-counted)
//! Lean code, which is exactly the "translates fine but is semantically
//! wrong" situation the test-runner's `known-failure` mechanism has no way
//! to represent (see `tests/README.md`). They exist here to be
//! mechanically re-checked (by inspecting the generated Lean) once
//! `simplify_duplicate_calls` gains an effect-awareness check, at which
//! point their `CURRENT (BUG):` tag should be deleted.
//!
//! Functions tagged `ASPIRATIONAL:` describe a desired invariant (e.g.
//! about implicit end-of-scope `Drop` glue for opaque types) that is not
//! independently confirmed to be modeled by the current pipeline; treat
//! their `EXPECTED` as a goal, not a verified guarantee (mirrors the
//! framing used throughout `lt-stateful-drop.rs`).
//!
//! Every other, untagged function in this file guards against regressions
//! in micro-passes that generalize a "looks the same, treat the same"
//! heuristic from pure values to effectful calls and backward
//! continuations without an accompanying effect analysis (CSE beyond
//! `simplify_duplicate_calls`, DCE, beta-reduction of inlined closures,
//! branch normalization, tuple/place projection rewriting, loop-body
//! normalization) — real concerns for a pipeline that already has one such
//! pass, even where no second pass is known to exist yet.
//!
//! Each function has a one-line `EXPECTED:` doc comment giving the exact
//! event order (and multiplicity) that must show up in the translation.

use core::marker::PhantomData;

// ---------------------------------------------------------------------------
// Opaque stateful resources: Lock / Guard / AutoGuard / Arc
// ---------------------------------------------------------------------------

/// Error returned by a fallible, non-blocking lock acquisition.
#[derive(Debug)]
pub enum LockError {
    Busy,
}

/// An opaque lock. Every method is a distinct, observable effect (it may
/// block, spin, update internal bookkeeping, etc.) that Aeneas cannot see
/// through.
#[verify::opaque]
pub struct Lock {
    _priv: (),
}

impl Lock {
    #[verify::opaque]
    pub fn new() -> Self {
        unimplemented!()
    }

    /// Blocking acquire: produces a manually-released `Guard`.
    #[verify::opaque]
    pub fn acquire(&self) -> Guard<'_> {
        unimplemented!()
    }

    /// Blocking acquire producing an auto-releasing `AutoGuard` (releases on
    /// `Drop`), used to test implicit-drop scenarios in isolation from the
    /// explicit-release `Guard` used everywhere else in this file.
    #[verify::opaque]
    pub fn acquire_auto(&self) -> AutoGuard<'_> {
        unimplemented!()
    }

    /// Non-blocking acquire: `Result`-shaped (nested `Ok`/`Err`) opaque call.
    #[verify::opaque]
    pub fn try_acquire(&self) -> Result<Guard<'_>, LockError> {
        unimplemented!()
    }

    /// Acquire that also hands back an auxiliary code, in one opaque call
    /// returning a tuple.
    #[verify::opaque]
    pub fn acquire_pair(&self) -> (Guard<'_>, i32) {
        unimplemented!()
    }

    /// Manually release a previously-acquired `Guard`. Consumes the guard;
    /// returns `Unit`.
    #[verify::opaque]
    pub fn release(&self, guard: Guard<'_>) {
        unimplemented!()
    }

    /// An effectful call whose forward result is `Unit` and which is never
    /// bound to any variable, not even `_`.
    #[verify::opaque]
    pub fn touch_unit(&self) {
        unimplemented!()
    }
}

/// An opaque, manually-released lock guard. Unlike `AutoGuard`, this type
/// does *not* implement `Drop`: its lifecycle is entirely explicit, via
/// `Lock::release`, so that most scenarios below can reason about a
/// syntactically visible call for every effect.
#[verify::opaque]
pub struct Guard<'a> {
    _lock: &'a Lock,
}

impl<'a> Guard<'a> {
    /// Opaque "backward" function: returns a mutable borrow into the data
    /// protected by the guard. Every call is a distinct effectful
    /// projection (it may, e.g., bump a generation counter internally).
    #[verify::opaque]
    pub fn touch(&mut self) -> &mut i32 {
        unimplemented!()
    }

    #[verify::opaque]
    pub fn get_value(&self) -> i32 {
        unimplemented!()
    }

    #[verify::opaque]
    pub fn set_value(&mut self, v: i32) {
        unimplemented!()
    }
}

/// An auto-releasing guard, mirroring a real `MutexGuard`: releases the lock
/// as an opaque effect when dropped, whether that drop is explicit
/// (`drop(g)`) or implicit (falling out of scope unused).
#[verify::opaque]
pub struct AutoGuard<'a> {
    _lock: &'a Lock,
}

impl<'a> Drop for AutoGuard<'a> {
    #[verify::opaque]
    fn drop(&mut self) {
        unimplemented!()
    }
}

/// An opaque, reference-counted handle, mirroring `std::sync::Arc`: cloning
/// and dropping are both observable effects (refcount increment/decrement),
/// even though every clone is indistinguishable from every other at the type
/// level.
#[verify::opaque]
pub struct Arc<T> {
    _v: PhantomData<T>,
}

impl<T> Arc<T> {
    #[verify::opaque]
    pub fn new(v: T) -> Self {
        unimplemented!()
    }

    #[verify::opaque]
    pub fn clone_arc(&self) -> Self {
        unimplemented!()
    }

    #[verify::opaque]
    pub fn get(&self) -> &T {
        unimplemented!()
    }
}

impl<T> Drop for Arc<T> {
    #[verify::opaque]
    fn drop(&mut self) {
        unimplemented!()
    }
}

/// A genuinely opaque, potentially-aliasing effectful function: takes two
/// mutable borrows that (in general callers of this signature) could
/// overlap. Used to test that repeated calls with the same-looking
/// arguments are not coalesced.
#[verify::opaque]
pub fn maybe_alias_effect(a: &mut i32, b: &mut i32) {
    unimplemented!()
}

/// A **pure** identity-on-a-mutable-borrow ("backward" function per Aeneas
/// terminology). Deliberately *not* opaque: Aeneas can see through this body
/// and knows it is pure (no hidden effect), so — unlike every opaque
/// backward function above — repeated calls to `identity_mut` on the same
/// place genuinely may be coalesced/CSE'd. This is the positive control for
/// `pure_backward_remains_optimizable` below.
pub fn identity_mut(x: &mut i32) -> &mut i32 {
    x
}

// ---------------------------------------------------------------------------
// 1. CSE must not merge distinct effectful calls
// ---------------------------------------------------------------------------

/// EXPECTED: acquire, release, acquire, release (4 distinct opaque calls;
/// the two `acquire`/`release` pairs must never be merged into one).
///
/// CURRENT (BUG): `l.acquire()` is called on the exact same free variable
/// `l` both times, with an intervening `l.release(g1)` that
/// `simplify_duplicate_calls` does not treat as invalidating its cache (see
/// the module doc above). The pass structurally caches the first
/// `l.acquire()` call and rewrites the second occurrence to reuse `g1`'s
/// result — `acquire` is invoked only once at runtime, and `g2` silently
/// aliases `g1`. This is a direct, currently-reproducing hit of that pass,
/// not a hypothetical.
pub fn two_identical_acquires_no_cse(l: &Lock) {
    let g1 = l.acquire();
    l.release(g1);
    let g2 = l.acquire();
    l.release(g2);
}

/// EXPECTED: clone_arc, clone_arc, drop(b1), drop(b2) (2 distinct clones,
/// each with its own drop; must not collapse to a single shared handle).
///
/// CURRENT (BUG): same direct hit as `two_identical_acquires_no_cse` above:
/// both `a.clone_arc()` calls are structurally identical (same `a`, no
/// other arguments), so `simplify_duplicate_calls` caches the first and
/// rewrites the second to reuse its result — the refcount is only
/// incremented once even though the source calls `clone_arc` twice.
pub fn two_identical_clones_no_cse(a: &Arc<i32>) {
    let b1 = a.clone_arc();
    let b2 = a.clone_arc();
    drop(b1);
    drop(b2);
}

/// EXPECTED: acquire, release, acquire, release, acquire, release (6
/// distinct opaque calls; three `acquire`/`release` pairs, none merged).
///
/// CURRENT (BUG): extends `two_identical_acquires_no_cse` to a third
/// repetition. `simplify_duplicate_calls`'s cache entry for `l.acquire()`
/// is added once (on the first occurrence) and persists for the rest of
/// the function body, so the second *and* third `l.acquire()` both get
/// rewritten to reuse the first result — this confirms the bug is not
/// limited to exactly two occurrences (e.g. a fix that only special-cases
/// pairs would still miss this).
pub fn three_identical_acquires_no_cse(l: &Lock) {
    let g1 = l.acquire();
    l.release(g1);
    let g2 = l.acquire();
    l.release(g2);
    let g3 = l.acquire();
    l.release(g3);
}

/// EXPECTED: acquire, acquire, release(g1), release(g2), in that exact
/// order; the two `release` call sites must not be merged into a single
/// call invoked once (which would release only one guard, or double-count).
///
/// CURRENT: unlike the two tests above, this shape's two `release` calls
/// take *different* free variables (`g1` vs `g2`) as their argument, so
/// `simplify_duplicate_calls` does not see them as structurally identical
/// on its own — this specific pairwise cache lookup does not fire directly.
/// It is nevertheless downstream of the same bug: the acquires are merged,
/// so both surviving release sites release the same guard `g1`; the second
/// acquire's independent guard never exists. The releases themselves are
/// not merged because their arguments differed when the pass ran.
pub fn two_identical_releases_no_cse(l: &Lock) {
    let g1 = l.acquire();
    let g2 = l.acquire();
    l.release(g1);
    l.release(g2);
}

// ---------------------------------------------------------------------------
// 2. DCE must not eliminate effectful calls with unused/Unit results
// ---------------------------------------------------------------------------

/// EXPECTED: touch_unit executes exactly once, even though its `()` result
/// is explicitly discarded via `let _ = ...`; a purity-based DCE pass must
/// not treat "result bound to `_`" as "call is dead".
///
/// CURRENT: this shape is *not* subject to the `simplify_duplicate_calls`
/// bug documented above — that pass only registers a call in its cache
/// when the binding pattern contains no ignored (`_`) variables, so a
/// `let _ = ...`-bound call is simply never cached in the first place. This
/// function instead exercises the orthogonal DCE hazard described by this
/// section's title.
pub fn infallible_unit_effect_bound_underscore_not_dced(l: &Lock) {
    let _ = l.touch_unit();
}

/// ASPIRATIONAL — EXPECTED: new(x), then an implicit `drop` of `_a` at end
/// of scope; the binding is never read, but `Arc::drop` is an opaque effect
/// that must still fire (DCE must not prune the whole construction+drop
/// pair just because the data itself is unused).
///
/// CURRENT: confirmed absent. Generated Lean contains `Arc.new` but no
/// implicit `Drop::drop` call.
pub fn unused_arc_must_drop(x: i32) {
    let _a = Arc::new(x);
}

/// ASPIRATIONAL — EXPECTED: acquire_auto, then an implicit `AutoGuard::drop`
/// (release) at end of scope; `_g` is unused as *data* but its drop is an
/// observable effect that must not be DCE'd.
///
/// CURRENT: confirmed absent. Generated Lean contains `acquire_auto` but no
/// implicit destructor call.
pub fn unused_guard_must_release(l: &Lock) {
    let _g = l.acquire_auto();
}

// ---------------------------------------------------------------------------
// 3. "No-op" effectful calls must still run
// ---------------------------------------------------------------------------

/// EXPECTED: get_value, set_value(v) — even though `set_value` writes back
/// exactly the value just read (a data-flow no-op), it is an opaque call
/// and must not be elided as an identity/no-op.
pub fn identity_setter_still_runs(g: &mut Guard<'_>) {
    let v = g.get_value();
    g.set_value(v);
}

/// EXPECTED: touch, touch — two distinct opaque backward calls on the same
/// guard, each performing its own write; the second must not be replaced by
/// reusing the first call's mutable reference.
pub fn repeated_deref_mut_preserves_order(g: &mut Guard<'_>) {
    let r1 = g.touch();
    *r1 += 1;
    let r2 = g.touch();
    *r2 += 2;
}

// ---------------------------------------------------------------------------
// 4. Beta-reduced closures must preserve call count
// ---------------------------------------------------------------------------

/// EXPECTED: touch_unit — the closure `touch_once` is applied exactly
/// once; inlining/beta-reducing it into `l.touch_unit()` must not change
/// that it fires exactly once.
///
/// The Bool output avoids the generated-Lean unit-output mismatch in
/// synthesized `FnMut.call_mut`. The explicit argument makes the closure
/// call shape visible to the optimizer.
pub fn beta_reduced_unit_closure_once(l: &Lock) {
    let touch_once = |tag: bool| {
        l.touch_unit();
        tag
    };
    touch_once(false);
}

/// EXPECTED: touch_unit, touch_unit — the same closure is applied twice;
/// the closure receives distinct tags, so even an effect-unaware structural
/// CSE cannot use the first call as the second call's result. Both
/// `touch_unit` effects must remain.
pub fn beta_reduced_unit_closure_twice(l: &Lock) {
    let touch_twice = |tag: bool| {
        l.touch_unit();
        tag
    };
    touch_twice(false);
    touch_twice(true);
}

// ---------------------------------------------------------------------------
// 5. Branching / control-flow joins must not merge or unconditionalize
//    effects
// ---------------------------------------------------------------------------

/// EXPECTED: if `flag`, exactly one acquire+release pair; if `!flag`,
/// exactly one (textually identical) acquire+release pair — but never
/// hoisted above the `if` to run unconditionally, and never merged across
/// the two arms into a single shared call.
///
/// CURRENT: renamed from `branch_hoisting_no_merge` — "hoisting" overclaimed
/// a specific optimization Aeneas does not have. There is no pass in
/// `src/pure/PureMicroPasses.ml` that moves an effectful statement sequence
/// out of both arms of an `if`/`match` to before it, or merges the two
/// arms' bodies (`simplify_let_branching`, the one branch-related pass in
/// the list, only rewrites the *pure tuple result* of a branch — e.g.
/// `let (b', x) := if b {(true, 1)} else {(false, 0)}` — it never touches
/// the effectful statements inside each arm). This remains a legitimate
/// forward-looking regression guard, not a currently-failing case.
pub fn if_branches_effects_remain_conditional(l: &Lock, flag: bool) {
    if flag {
        let g = l.acquire();
        l.release(g);
    } else {
        let g = l.acquire();
        l.release(g);
    }
}

/// EXPECTED: if `flag`, acquire+release; if `!flag`, clone_arc+drop —
/// exactly one branch's effects fire, never both, and the optimizer must
/// not assume the two branches are "equivalent effects" and collapse them.
///
/// CURRENT: renamed from `branch_hoisting_distinct_effects_no_merge` for
/// the same reason as `if_branches_effects_remain_conditional` above — see
/// its doc comment.
pub fn if_branches_distinct_effects_not_conflated(l: &Lock, a: &Arc<i32>, flag: bool) {
    if flag {
        let g = l.acquire();
        l.release(g);
    } else {
        let b = a.clone_arc();
        drop(b);
    }
}

/// EXPECTED: if `flag`, acquire+release; if `!flag`, zero opaque calls —
/// the empty `else` arm must not cause the compiler to conclude the whole
/// conditional is effect-free and prune the `true` arm's calls.
pub fn dead_branch_one_arm_pure(l: &Lock, flag: bool) {
    if flag {
        let g = l.acquire();
        l.release(g);
    }
}

/// EXPECTED: an `if let` nested inside a `match` arm reaches `acquire` +
/// `release` only when `opt = Some(0)`; every other combination of `opt`
/// (a different `Some(v)`, or `None`) performs zero opaque calls — a
/// control-flow-join normalization pass must not conflate the nested
/// `match`/`if let` structure into a shape that changes which combination
/// of runtime values reaches the opaque call.
pub fn nested_if_let_then_match_effect_order(l: &Lock, opt: Option<i32>) -> i32 {
    if let Some(v) = opt {
        match v {
            0 => {
                let g = l.acquire();
                l.release(g);
                0
            }
            _ => v,
        }
    } else {
        -1
    }
}

// ---------------------------------------------------------------------------
// 6. Tuple / Result decomposition must evaluate the opaque call exactly once
// ---------------------------------------------------------------------------

/// EXPECTED: acquire_pair evaluated exactly once, producing both `g` and
/// `code` together; release(g) once; a naive tuple-projection rewrite that
/// replaces each component use with a fresh call to `acquire_pair()` would
/// be unsound here.
pub fn tuple_decomposition_single_eval(l: &Lock) -> i32 {
    let (g, code) = l.acquire_pair();
    l.release(g);
    code
}

/// EXPECTED: try_acquire evaluated exactly once; `release` occurs only in
/// the `Ok` arm; the `Err` arm has zero opaque calls; the two arms' effects
/// must not be hoisted into a shared prefix before the `match`.
pub fn nested_result_shaped_effect(l: &Lock) -> i32 {
    match l.try_acquire() {
        Ok(g) => {
            l.release(g);
            1
        }
        Err(LockError::Busy) => 0,
    }
}

/// EXPECTED: acquire, acquire, release(g1), release(g2) — both elements of
/// the tuple literal `(l.acquire(), l.acquire())` are evaluated left to
/// right, each a distinct effect, before the tuple is destructured.
///
/// CURRENT (BUG): the two tuple elements are, once desugared, two
/// structurally-identical `l.acquire()` calls with no argument
/// differences — exactly the shape `simplify_duplicate_calls` (see the
/// module doc above) collapses. This is another direct hit of that pass,
/// via a tuple-literal binding rather than two sequential `let`s.
pub fn identical_effects_tuple_no_cse(l: &Lock) -> i32 {
    let (g1, g2) = (l.acquire(), l.acquire());
    l.release(g1);
    l.release(g2);
    0
}

/// EXPECTED: acquire, tuple destructure (plain `let`), release; acquire_pair,
/// tuple destructure (pattern binding), release; try_acquire, match binding,
/// release — three structurally-similar-looking acquire effects, each
/// consumed through a *different* binding shape (plain `let`, tuple
/// destructure, `match` arm pattern). A place/binding-shape normalization
/// pass must not conflate these into a single canonical shape and thereby
/// merge or drop any of the three underlying opaque calls.
pub fn different_binding_shapes_preserve_effects(l: &Lock) -> i32 {
    let g1 = l.acquire();
    l.release(g1);
    let (g2, code) = l.acquire_pair();
    l.release(g2);
    match l.try_acquire() {
        Ok(g3) => l.release(g3),
        Err(LockError::Busy) => {}
    }
    code
}

// ---------------------------------------------------------------------------
// 7. Unit-returning effects and "data-less" backward continuations
// ---------------------------------------------------------------------------

/// EXPECTED: touch_unit fires exactly once as a bare statement (no binder
/// at all, not even `_`); DCE must not strip it merely because it produces
/// no data.
pub fn effectful_call_returns_unit(l: &Lock) {
    l.touch_unit();
}

/// EXPECTED: touch, then a write through the returned reference — the
/// function's own forward output is `Unit`; the only observable effect is
/// the opaque backward update propagated through `g` (an effectful "back"
/// with no accompanying data output). Must not be treated as dead just
/// because nothing is returned.
pub fn effectful_backward_no_data_output(g: &mut Guard<'_>) {
    let r = g.touch();
    *r = 42;
}

// ---------------------------------------------------------------------------
// 8. Pure and effectful calls interleaved
// ---------------------------------------------------------------------------

/// EXPECTED: acquire, release occur in that relative order and are never
/// reordered past each other; the pure arithmetic (`y`, `z`, final sum) may
/// be freely reassociated/hoisted by the optimizer since it carries no
/// effect, but must not cause acquire/release to be duplicated or dropped.
pub fn pure_and_effectful_interleaved(l: &Lock, x: i32) -> i32 {
    let y = x + 1;
    let g = l.acquire();
    let z = y * 2;
    l.release(g);
    z + 3
}

/// EXPECTED: `x * x + 1` is computed identically both before and after
/// `acquire`/`release`; whether or not the optimizer lifts/coalesces this
/// *pure* repeated subexpression across the call (it legitimately may —
/// this is a positive control, unlike the opaque calls tested elsewhere in
/// this file), `acquire` and `release` must still each fire exactly once,
/// in that relative order, undisturbed by any such lifting.
pub fn lifted_arithmetic_order_repeated_pure_expr(l: &Lock, x: i32) -> i32 {
    let p1 = x * x + 1;
    let g = l.acquire();
    let p2 = x * x + 1;
    l.release(g);
    p1 + p2
}

/// EXPECTED: get_value, get_value — both operands of the pure-looking `+`
/// expression are opaque reads; even though the expression as a whole has
/// no visible effect on the caller's data, each read is a distinct
/// observable event (e.g. it could bump an internal access counter) and
/// must not be merged into a single read reused twice.
///
/// CURRENT (BUG): both calls are `g.get_value()` on the same `g`, with no
/// other arguments — a direct hit of `simplify_duplicate_calls` (see the
/// module doc above), this time surfacing through operands of a pure binary
/// expression rather than two sequential `let`s.
pub fn identical_effects_pure_expr_no_cse(g: &Guard<'_>) -> i32 {
    g.get_value() + g.get_value()
}

// ---------------------------------------------------------------------------
// 9. Array / slice index-projection identity
// ---------------------------------------------------------------------------

/// EXPECTED: acquire(locks[i]), release(locks[i]), acquire(locks[j]),
/// release(locks[j]) — four opaque calls at the two (possibly-equal at
/// runtime) indices `i` and `j`; a place-projection canonicalization pass
/// must not conflate `locks[i]` and `locks[j]` into one symbolic place.
///
/// CURRENT: renamed from `array_slice_mut_projection_rewrite`, and the
/// parameter changed from `&mut [Lock]` to `&[Lock]` — `Lock::acquire` and
/// `Lock::release` both take `&self`, so no mutable projection is actually
/// exercised here; the original name's "mut" overclaimed what this test
/// covers. What *is* tested is place-projection identity: `locks[i]` and
/// `locks[j]` must remain distinct symbolic places through shared-borrow
/// indexing.
pub fn array_index_projection_no_coalescing(locks: &[Lock], i: usize, j: usize) {
    let gi = locks[i].acquire();
    locks[i].release(gi);
    let gj = locks[j].acquire();
    locks[j].release(gj);
}

/// EXPECTED: acquire(locks[i]), release(locks[i]), acquire(locks[i + 1]),
/// release(locks[i + 1]) — same shape as above but stressing two index
/// *expressions* built from the same base variable (`i` vs `i + 1`) rather
/// than two independent index variables.
///
/// CURRENT: parameter changed from `&mut [Lock]` to `&[Lock]` for the same
/// reason as `array_index_projection_no_coalescing` above — no mutable
/// access is actually required.
pub fn array_projection_no_coalescing_same_syntax_diff_index(locks: &[Lock], i: usize) {
    let g0 = locks[i].acquire();
    locks[i].release(g0);
    let g1 = locks[i + 1].acquire();
    locks[i + 1].release(g1);
}

// ---------------------------------------------------------------------------
// 10. Pure backwards remain optimizable (positive controls)
// ---------------------------------------------------------------------------

/// EXPECTED: `identity_mut` is pure/transparent, not opaque — unlike every
/// effectful-backward case above, the optimizer *may* legitimately
/// coalesce/CSE the two backward continuations of `identity_mut(x)`, since
/// both return the exact same place with no hidden effect. This is the
/// positive control: a fix for the effectful cases above must not become so
/// conservative that it also blocks optimization here.
pub fn pure_backward_remains_optimizable(x: &mut i32) -> i32 {
    let r1 = identity_mut(x);
    *r1 += 1;
    let r2 = identity_mut(x);
    *r2 += 1;
    *x
}

/// EXPECTED: `&mut arr[i]` is a *real* (not `#[verify::opaque]`) backward
/// function — Aeneas's own built-in `IndexMut`/slice-indexing translation,
/// the same kind of continuation exercised by every opaque example above,
/// but here through Aeneas's native, non-opaque machinery. Applied twice at
/// the identical index `i`, each call is a distinct built-in projection
/// into `*arr`; the two writes (`+= 1` then `+= 2`) must be observed in
/// program order, mirroring `repeated_deref_mut_preserves_order` above but
/// for the built-in case. This is a second positive control: it confirms
/// Aeneas's own backward-function machinery (not just our opaque stand-ins)
/// already gets repeated-index writes right, giving the rest of this file's
/// opaque hazards a real, non-opaque point of comparison.
pub fn real_index_mut_backward_repeated_write(arr: &mut [i32], i: usize) {
    let r1 = &mut arr[i];
    *r1 += 1;
    let r2 = &mut arr[i];
    *r2 += 2;
}

// ---------------------------------------------------------------------------
// 11. Effect order across independent opaque resources
// ---------------------------------------------------------------------------

/// EXPECTED: acquire, clone_arc, release, drop(b), strictly in program
/// order — even though `Lock` and `Arc` are independent resources with no
/// shared data, there is no commutation rule in the translation and the
/// literal statement order must be preserved.
pub fn effect_order_around_opaque_calls(l: &Lock, a: &Arc<i32>) {
    let g = l.acquire();
    let b = a.clone_arc();
    l.release(g);
    drop(b);
}

/// EXPECTED: acquire, clone_arc, drop(b), release — a second interleaving
/// shape (clone/drop nested strictly between acquire and release) to
/// confirm ordering is preserved regardless of how the two resources'
/// lifetimes are nested relative to one another.
pub fn interleaved_clone_and_lock_effects(l: &Lock, a: &Arc<i32>) {
    let g = l.acquire();
    let b = a.clone_arc();
    drop(b);
    l.release(g);
}

// ---------------------------------------------------------------------------
// 12. No coalescing across a call that could alias its arguments
// ---------------------------------------------------------------------------

/// EXPECTED: maybe_alias_effect, maybe_alias_effect — two distinct calls
/// with the same-looking argument list; since the callee is opaque and
/// takes two `&mut i32` that could (for other instantiations of this
/// signature) overlap, the first call's effect on `*x`/`*y` cannot be
/// assumed irrelevant to the second — CSE must not collapse them into one
/// call reused twice.
///
/// CURRENT: this does not reproduce `simplify_duplicate_calls`. Aeneas
/// threads mutable arguments by value, so the second call receives the
/// first call's backward outputs rather than the original `x` and `y`.
/// This remains a guard against a future alias-normalizing CSE.
pub fn no_coalescing_alias_capable_call(x: &mut i32, y: &mut i32) {
    maybe_alias_effect(x, y);
    maybe_alias_effect(x, y);
}

/// EXPECTED: maybe_alias_effect(x, y), maybe_alias_effect(y, x) — the same
/// two variables, in swapped argument order, on the second call; a
/// commutativity-aware CSE (smarter than today's purely-syntactic
/// `simplify_duplicate_calls`, which does not attempt this) must not treat
/// the swapped-argument call as "the same effect, just permuted" and merge
/// it with the first.
///
/// CURRENT: like `no_coalescing_alias_capable_call` above, this does
/// *not* currently reproduce the `simplify_duplicate_calls` bug — the two
/// calls' argument lists (`(x, y)` vs `(y, x)`) are not structurally equal,
/// so the pass's plain `TExprMap` lookup does not fire. This is a
/// forward-looking guard against a smarter, commutativity-aware future
/// pass, not a currently-failing case.
pub fn aliasing_params_swapped_order_no_merge(x: &mut i32, y: &mut i32) {
    maybe_alias_effect(x, y);
    maybe_alias_effect(y, x);
}

// ---------------------------------------------------------------------------
// 13. Clone/drop counts must be individually observable
// ---------------------------------------------------------------------------

/// EXPECTED: new(x), clone_arc -> b, clone_arc -> c, drop(b) [explicit],
/// then implicit drop(c), implicit drop(a) at end of scope in reverse
/// declaration order — 6 distinct effectful events, none merged or elided
/// even though `b` and `c` are clones of the same `a` and are
/// type-indistinguishable.
///
/// CURRENT (BUG) + ASPIRATIONAL: two separate caveats apply here.
/// (1) `CURRENT (BUG)`: `b = a.clone_arc()` and `c = a.clone_arc()` are
/// structurally identical (same `a`, no other arguments) — the same direct
/// `simplify_duplicate_calls` hit as `two_identical_clones_no_cse` (see the
/// module doc above), so `c` is expected to silently alias `b` today rather
/// than triggering a second, independent clone.
/// (2) `ASPIRATIONAL`: the *implicit* end-of-scope drops of `c` and `a` are
/// confirmed absent from today's generated Lean; only explicit `drop(b)`
/// appears.
pub fn clone_drop_count_observable(x: i32) {
    let a = Arc::new(x);
    let b = a.clone_arc();
    let c = a.clone_arc();
    drop(b);
}

/// EXPECTED: new(x), new(y), drop(old) [explicit, holding the `Arc::new(x)`
/// value], then implicit drop(a) [holding `Arc::new(y)`] at end of scope —
/// 4 distinct effectful events; reassigning `a` via `mem::replace` must not
/// let the optimizer conclude the original `Arc::new(x)` was "dead" and
/// elide either its construction or its matching drop.
///
/// ASPIRATIONAL (partial): the explicit `new(x)`, `new(y)`, and `drop(old)`
/// events are solid, non-aspirational expectations. Only the final
/// *implicit* end-of-scope `drop(a)` is confirmed absent from today's
/// generated Lean.
pub fn clone_drop_count_observable_reassign(x: i32, y: i32) {
    let mut a = Arc::new(x);
    let old = core::mem::replace(&mut a, Arc::new(y));
    drop(old);
}

/// EXPECTED: acquire, acquire, release(old), release(g) — `g` is replaced
/// mid-lifetime via `mem::replace` while it still holds a live (unreleased)
/// guard; both the original guard (`old`, released explicitly) and the
/// replacement (`g`, released at the end) must reach their own `release`
/// call. A "variable reassignment" normalization must not lose the first
/// guard's release, duplicate it, or attribute both releases to the same
/// acquire.
///
/// CURRENT (BUG): the initial `l.acquire()` and the `l.acquire()` passed as
/// `mem::replace`'s second argument are structurally identical (same `l`,
/// no other arguments) — another direct hit of `simplify_duplicate_calls`
/// (see the module doc above): the second `acquire` is expected to
/// silently reuse the first's result instead of running again.
pub fn guard_replace_no_lost_effects(l: &Lock) {
    let mut g = l.acquire();
    let old = core::mem::replace(&mut g, l.acquire());
    l.release(old);
    l.release(g);
}

// ---------------------------------------------------------------------------
// 14. Actual loops: iteration must not be collapsed, hoisted, or reordered
// ---------------------------------------------------------------------------
//
// Every hazard above was demonstrated with straight-line code. Real loop
// bodies introduce their own normalization passes (`loops_to_recursive`,
// `simplify_loop_output_conts`, `filter_loop_useless_inputs_outputs`,
// `reorder_loop_inputs`/`reorder_loop_outputs` in
// `src/pure/PureMicroPasses.ml`) that operate on the recursive function
// Aeneas introduces for each loop. The functions below are this suite's
// *actual* Rust `for` loops that are confirmed to
// translate successfully today — every case above uses straight-line
// repetition instead. A fourth loop shape, `loop_break_preserves_order`
// (a `for` loop containing a `break`), currently does not translate at
// all — Aeneas' loop-context matching fails on it (`Could not match the
// contexts`, `interp/InterpJoin.ml`) independently of anything this file
// is about (opaque-effect duplication/ordering). That shape has been
// moved to `lt-stateful-pass-known-failures.rs` (see that file's module
// doc) so this file's contexts keep matching.

/// EXPECTED: acquire, release, acquire, release, ..., exactly `n` times —
/// one acquire/release pair per iteration; the loop-body normalization
/// passes must not hoist the acquire out of the loop (running it once
/// before iterating) nor merge/CSE the identical-looking call across
/// iterations into a single call reused `n` times.
pub fn loop_repeated_acquire_release(l: &Lock, n: usize) {
    for _ in 0..n {
        let g = l.acquire();
        l.release(g);
    }
}

/// EXPECTED: touch fires exactly `n` times, each write building on the
/// previous one (`*r += 1` each iteration) — the opaque backward
/// continuation `g.touch()` is threaded across loop iterations (its result
/// on iteration `k` depends on the write from iteration `k - 1`), unlike
/// every other backward-function test in this file, which only chains
/// continuations within a single straight-line body. A loop-carried-value
/// analysis must not treat each iteration's `touch()` as independent of the
/// others, nor coalesce them into a single call outside the loop.
pub fn loop_carried_backward_update(g: &mut Guard<'_>, n: usize) {
    for _ in 0..n {
        let r = g.touch();
        *r += 1;
    }
}

/// EXPECTED: touch_unit fires exactly `n` times, once per iteration, even
/// though its `()` result is never bound to anything (not even `_`); a
/// purity/DCE-based loop-body simplification must not conclude the loop
/// body is a no-op (since it produces no data at all) and eliminate the
/// loop entirely.
pub fn unit_effect_loop_iteration(l: &Lock, n: usize) {
    for _ in 0..n {
        l.touch_unit();
    }
}
