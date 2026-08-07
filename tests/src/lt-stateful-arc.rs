//@ [!lean] skip
//! EXPECTED AFTER IMPLEMENTATION:
//! This file complements `lt-stateful-signatures.rs` (guard acquire/release)
//! and the `Arc<T>` micro-pass fixtures in `lt-stateful-passes.rs`
//! (effectful-call ordering) with a dedicated fixture set for the
//! **strong/weak reference-counting lifecycle** of `Arc`/`Weak`-shaped
//! values: allocation, cloning, downgrading, upgrading, and every way a
//! strong or weak owner can be released (implicit end-of-scope drop,
//! explicit `drop`, `Option::take`, overwriting a binding, moving into or
//! returning from a helper function, ...). Once a future ITree "stateful
//! Arc/Weak events" pass is implemented (a generalization of the
//! `#[verify::stateful_lifetimes]` feature explored in
//! `lt-stateful-signatures.rs`, `lt-stateful-reborrows.rs`,
//! `lt-stateful-wrappers.rs`, `lt-stateful-drop.rs`, and
//! `lt-stateful-control.rs` from guard-shaped resources to reference-counted
//! ones), it is expected to translate:
//!   - `Arc::new` as an "owner created" event, with the strong count
//!     starting at exactly 1.
//!   - `Arc::clone_arc` / `Weak::clone_weak` as count-increment events (strong
//!     and weak respectively), each requiring its own matching release.
//!   - Every place a strong or weak owner is released -- implicit
//!     end-of-scope drop, explicit `drop(...)`, `Option::take`, overwriting
//!     a `let mut` binding, one arm of an `if`/`match` -- as a
//!     count-decrement event at that exact program point, exactly the way
//!     `lt-stateful-drop.rs` tracks guard releases through ordinary Rust
//!     drop-scope rules.
//!   - `Arc::downgrade` / `Weak::upgrade` as the bridge between the strong
//!     and weak count-observations: `upgrade` must be modeled as depending
//!     on whether the strong count is still positive at the call site
//!     (`Some`) or has already reached zero (`None`).
//!   - `Arc<Lock<T>>` (a shared, lock-protected value) as the composition of
//!     this feature with the guard acquire/release bookkeeping from
//!     `lt-stateful-signatures.rs`: reaching the `Lock` through the `Arc`
//!     must not change how the guard's own acquire/release pair is
//!     threaded.
//!   - A strong reference cycle (two nodes whose `next` fields strongly
//!     own each other, see section 10 below) as an ordinary pair of
//!     count-increment events like any other `clone_arc`: this feature
//!     only tracks count-increment / count-decrement events, never
//!     whole-graph reachability, so it is **not** expected to detect or
//!     flag the resulting leak on its own -- documented as **known
//!     unsupported / future work**, the same status as the `Scope`
//!     borrow-tracking limitation in
//!     `lt-stateful-concurrency-known-failures.rs`.
//!
//! CURRENT BASELINE:
//! `#[verify::stateful_lifetimes]` is an inert tool attribute today
//! (registered via `#![register_tool(verify)]` but not yet interpreted by
//! Aeneas). `Arc<T>`, `Weak<T>`, `Lock<T>`, `ReadGuard`, and `WriteGuard`
//! are all `#[verify::opaque]`, so every method call on them -- `new`,
//! `clone_arc`, `get`, `downgrade`, `clone_weak`, `upgrade`,
//! `strong_count`, `weak_count`, `read`, `write`, `release` -- is extracted
//! today as an ordinary opaque call, with no refcount reasoning whatsoever.
//! `Arc<T>` and `Weak<T>` each carry an opaque `drop` method, but Aeneas
//! currently emits no implicit end-of-scope destructor glue. Their implicit
//! release claims are therefore aspirational: generated Lean records the
//! explicit ownership operations and `core::mem::drop` calls, but not a call
//! to the destructor itself. Fixtures in this file deliberately use
//! distinct receivers/arguments where repeated observations are required,
//! so the current structural CSE cannot collapse them; the direct CSE
//! reproducers live in `lt-stateful-passes.rs`.
//! Every function in this file is required to be valid, borrow-checked
//! Rust and is expected to keep translating today exactly as any other
//! opaque-call fixture does; none of them are ever actually executed (no
//! `main`, no `#[verify::test]`), since `Arc`/`Weak` are opaque and their
//! side effects are unimplemented stubs.
#![feature(register_tool)]
#![register_tool(verify)]

use std::marker::PhantomData;

// ---------------------------------------------------------------------
// Opaque Arc<T> / Weak<T> prelude
// ---------------------------------------------------------------------

/// An opaque, reference-counted strong owner, mirroring `std::sync::Arc`:
/// allocating, cloning, and dropping are all observable effects (refcount
/// increment/decrement), even though every clone is indistinguishable from
/// every other at the type level. Modeled abstractly (`PhantomData`, no
/// real allocation or atomic refcount) so Aeneas sees a symbolic opaque
/// value, exactly like `Lock`/`Guard` in `lt-stateful-signatures.rs`.
#[verify::opaque]
pub struct Arc<T> {
    _marker: PhantomData<T>,
}

/// An opaque, non-owning handle produced by `Arc::downgrade`, mirroring
/// `std::sync::Weak`. Does not keep the pointee alive on its own; whether
/// `upgrade` can recover a strong owner depends on whether any `Arc` for
/// the same value is still alive at the call site.
#[verify::opaque]
pub struct Weak<T> {
    _marker: PhantomData<T>,
}

impl<T> Arc<T> {
    /// Allocate a new strong owner. EXPECTED: an "owner created" event;
    /// strong count starts at 1, weak count at 0.
    #[verify::opaque]
    pub fn new(_value: T) -> Self {
        unimplemented!()
    }

    /// Shared, read-only projection into the pointee. EXPECTED: a pure
    /// projection, no count-changing event of its own (mirrors
    /// `ReadGuard::get` in `lt-stateful-signatures.rs`).
    #[verify::opaque]
    pub fn get(&self) -> &T {
        unimplemented!()
    }

    /// Create another strong owner of the same value. EXPECTED: increments
    /// the strong count by one; every clone (the original included) must be
    /// released for the pointee itself to be released.
    #[verify::opaque]
    pub fn clone_arc(&self) -> Self {
        unimplemented!()
    }

    /// Number of live strong owners. EXPECTED: a pure observation of the
    /// stateful strong-refcount, kept in sync with `clone_arc` and every
    /// strong `Drop`.
    #[verify::opaque]
    pub fn strong_count(&self) -> usize {
        unimplemented!()
    }

    /// Number of live weak owners. EXPECTED: symmetric to `strong_count`,
    /// kept in sync with `downgrade`, `clone_weak`, and every weak `Drop`.
    #[verify::opaque]
    pub fn weak_count(&self) -> usize {
        unimplemented!()
    }

    /// Create a non-owning `Weak` handle. EXPECTED: increments the weak
    /// count; does not affect the strong count or extend the pointee's
    /// lifetime.
    #[verify::opaque]
    pub fn downgrade(&self) -> Weak<T> {
        unimplemented!()
    }
}

/// EXPECTED release point: wherever ordinary Rust drop-scope rules say this
/// `Arc`'s scope ends. Decrements the strong count; once it reaches zero,
/// the pointee itself would be released (modeled here as an opaque no-op,
/// since these fixtures are never executed).
impl<T> Drop for Arc<T> {
    #[verify::opaque]
    fn drop(&mut self) {
        unimplemented!()
    }
}

impl<T> Weak<T> {
    /// Construct a dangling weak handle that points to no allocation.
    /// EXPECTED: `upgrade` always returns `None`; no refcount is allocated.
    #[verify::opaque]
    pub fn new() -> Self {
        unimplemented!()
    }

    /// Clone a weak handle independently of the strong owner it was
    /// downgraded from. EXPECTED: increments the weak count only.
    #[verify::opaque]
    pub fn clone_weak(&self) -> Self {
        unimplemented!()
    }

    /// Attempt to recover a strong owner. EXPECTED: `Some` (with a *new*
    /// strong owner, itself requiring its own release) while at least one
    /// strong owner is alive at the call site; `None` once the last strong
    /// owner has already been dropped -- exactly the distinction this
    /// future feature must track.
    #[verify::opaque]
    pub fn upgrade(&self) -> Option<Arc<T>> {
        unimplemented!()
    }
}

/// EXPECTED release point for a weak handle: decrements the weak count
/// only, with no effect on the strong count or the pointee's lifetime.
impl<T> Drop for Weak<T> {
    #[verify::opaque]
    fn drop(&mut self) {
        unimplemented!()
    }
}

// ---------------------------------------------------------------------
// Opaque Lock<T> / ReadGuard / WriteGuard prelude (for `Arc<Lock<T>>`)
// ---------------------------------------------------------------------

/// Opaque lock guarding a `T`, reused here (in miniature) so we can model
/// the common `Arc<Lock<T>>` shared-mutable-state pattern. See
/// `lt-stateful-signatures.rs` for the full guard/release fixture set;
/// duplicated here so this file has no cross-file dependency (as is the
/// case for every `Lock`/`Guard` prelude across the `lt-stateful-*` files).
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
// Plain (non-opaque) structs used to exercise "Arc in a struct/list" shapes
// ---------------------------------------------------------------------

/// A singly-linked chain node, the classic shared-linked-list shape: each
/// node's tail is an `Option<Arc<Node>>` rather than a plain `Box`.
///
/// The recursive layout is opaque to Aeneas because Lean cannot establish
/// strict positivity through an abstract `Arc` type constructor.
#[verify::opaque]
pub struct Node {
    pub value: i32,
    pub next: Option<Arc<Node>>,
}

impl Node {
    #[verify::opaque]
    pub fn new(_value: i32, _next: Option<Arc<Node>>) -> Self {
        unimplemented!()
    }

    #[verify::opaque]
    pub fn value(&self) -> i32 {
        unimplemented!()
    }
}

/// A value with a name, used as the target of a `Weak` back-pointer below.
pub struct Parent {
    pub name: i32,
}

/// A struct holding a non-owning `Weak` back-pointer to its `Parent`, the
/// classic pattern used to avoid parent/child reference cycles.
pub struct Child {
    pub parent: Weak<Parent>,
}

// ---------------------------------------------------------------------
// 1. Construction and multiple strong owners
// ---------------------------------------------------------------------

/// `Arc::new` shape: allocate a single strong owner and read through it.
/// EXPECTED: the allocation site is the unique "owner created" event;
/// `get` remains a pure projection.
#[verify::stateful_lifetimes]
pub fn arc_new_basic(value: i32) -> i32 {
    let a = Arc::new(value);
    *a.get()
}

/// One extra strong owner via `clone_arc`. EXPECTED: strong count goes
/// 1 -> 2 while both `a` and `b` are alive, back to 0 once both are
/// dropped at the end of the function.
#[verify::stateful_lifetimes]
pub fn arc_clone_once(value: i32) -> (i32, i32) {
    let a = Arc::new(value);
    let b = a.clone_arc();
    (*a.get(), *b.get())
}

/// Two extra strong owners via `clone_arc`, three owners total (`a`, `b`,
/// `c`). EXPECTED: strong count reaches 3 before any of them is dropped.
/// The second clone uses `b` as its receiver so current structural CSE
/// cannot collapse it with the first clone.
#[verify::stateful_lifetimes]
pub fn arc_clone_twice(value: i32) -> (i32, i32, i32) {
    let a = Arc::new(value);
    let b = a.clone_arc();
    let c = b.clone_arc();
    (*a.get(), *b.get(), *c.get())
}

// ---------------------------------------------------------------------
// 2. Drop: implicit / explicit / last-strong / overwrite
// ---------------------------------------------------------------------

/// Implicit drop: `a` goes out of scope at the closing `}` of the inner
/// block, with no explicit `drop` call. EXPECTED: the block's closing
/// brace is the "owner released" event (strong count 1 -> 0).
#[verify::stateful_lifetimes]
pub fn arc_drop_implicit_end_of_scope(value: i32) {
    {
        let a = Arc::new(value);
        let _ = a.get();
    }
    // `a` has already been (implicitly) dropped here.
}

/// Explicit drop via `std::mem::drop`. EXPECTED: the `drop(a)` call site
/// is itself the "owner released" event, rather than a scope-exit.
#[verify::stateful_lifetimes]
pub fn arc_drop_explicit_via_std_drop(value: i32) {
    let a = Arc::new(value);
    drop(a);
}

/// Last-strong-owner behavior: `a` is created, `b` clones it, then both
/// are dropped in sequence. EXPECTED: dropping `a` first merely decrements
/// the strong count 2 -> 1; only the *second* `drop` (of `b`, now the last
/// remaining strong owner) is the point at which the pointee would
/// actually be released (1 -> 0).
#[verify::stateful_lifetimes]
pub fn arc_last_strong_drop_order(value: i32) {
    let a = Arc::new(value);
    let b = a.clone_arc();
    drop(a);
    drop(b);
}

/// Overwriting a binding that already holds an `Arc`. EXPECTED: assigning
/// `a = Arc::new(2)` implicitly drops the *old* value of `a` (releasing
/// the first owner) before installing the new one; the new owner is then
/// released at the end of the function.
#[verify::stateful_lifetimes]
pub fn arc_overwrite_binding() {
    let mut a = Arc::new(1);
    let _ = a.get();
    a = Arc::new(2);
    let _ = a.get();
}

// ---------------------------------------------------------------------
// 3. Arc in collections / structs
// ---------------------------------------------------------------------

/// `Option<Arc<T>>`: holding, then removing (`take`) the strong owner.
/// EXPECTED: `take` transfers ownership out of the `Option` -- leaving
/// `None` behind -- without releasing the extracted value itself; the
/// extracted value is then released explicitly.
#[verify::stateful_lifetimes]
pub fn arc_in_option_some_and_take(value: i32) -> bool {
    let mut slot: Option<Arc<i32>> = Some(Arc::new(value));
    let taken = slot.take();
    let was_some = taken.is_some();
    if let Some(a) = taken {
        drop(a);
    }
    was_some
}

/// `Option<Arc<T>>` left untouched (no explicit `take`) until the end of
/// the function. EXPECTED: unlike `arc_in_option_some_and_take` above,
/// there is no explicit "owner released" event anywhere in the function
/// body -- the `Option`'s own scope-exit drop glue is the *only* release
/// point, exactly the way a bare (non-`Option`) `Arc` binding is released
/// implicitly.
#[verify::stateful_lifetimes]
pub fn arc_in_option_implicit_drop(value: i32) -> bool {
    let slot: Option<Arc<i32>> = Some(Arc::new(value));
    slot.is_some()
    // `slot` (and the strong owner inside it) is dropped implicitly here,
    // at the closing brace of the function body.
}

/// Several strong owners collected in a `Vec`, all released together when
/// the vector itself is dropped. EXPECTED: one "owner released" event per
/// element, triggered by the vector's own `Drop` glue.
#[verify::stateful_lifetimes]
pub fn arc_in_vec_pushed_and_dropped(values: Vec<i32>) {
    let mut owners: Vec<Arc<i32>> = Vec::new();
    for v in values {
        owners.push(Arc::new(v));
    }
    // `owners` (and every `Arc` it contains) is dropped here.
}

/// Removing the first owner from a `Vec` via `Vec::remove`,
/// which shifts every following element down by one index and preserves
/// their relative order. EXPECTED: `remove` transfers ownership of the
/// extracted `Arc` out of the vector -- it is not itself an "owner
/// released" event -- while every remaining owner keeps its own
/// independent event history, now reachable through a different index.
#[verify::stateful_lifetimes]
pub fn arc_vec_remove_preserves_order(values: Vec<i32>) -> (i32, i32) {
    let mut owners: Vec<Arc<i32>> = Vec::new();
    for v in values {
        owners.push(Arc::new(v));
    }
    let removed = owners.remove(0);
    let removed_value = *removed.get();
    drop(removed);
    let first_remaining = if owners.is_empty() {
        -1
    } else {
        *owners[0].get()
    };
    (removed_value, first_remaining)
    // The remaining owners in `owners` are released here, in whatever
    // order `Vec`'s own drop glue visits them.
}

/// Removing an owner via `Vec::swap_remove`, which instead moves the
/// *last* element into the removed slot (O(1), but does not preserve
/// order). EXPECTED: exactly like `remove`, the extracted `Arc` is
/// transferred out (not released by `swap_remove` itself); the only
/// difference from `remove` is *which* remaining owner ends up at the
/// removed index, never the total number of "owner released" events at
/// the end of the function.
#[verify::stateful_lifetimes]
pub fn arc_vec_swap_remove_reorders(values: Vec<i32>) -> (i32, i32) {
    let mut owners: Vec<Arc<i32>> = Vec::new();
    for v in values {
        owners.push(Arc::new(v));
    }
    let removed = owners.swap_remove(0);
    let removed_value = *removed.get();
    drop(removed);
    let first_remaining = if owners.is_empty() {
        -1
    } else {
        *owners[0].get()
    };
    (removed_value, first_remaining)
    // The remaining owners in `owners` (now reordered) are released here.
}

/// An `Arc` stored inside a recursive struct field (`Node::next`), the
/// classic shared-linked-list shape. EXPECTED: building the chain performs
/// one "owner created" event per `Arc::new`; dropping `head` cascades
/// through `next` down the chain.
#[verify::stateful_lifetimes]
pub fn arc_in_node_struct_chain() -> i32 {
    let tail = Node::new(2, None);
    let head = Node::new(1, Some(Arc::new(tail)));
    head.value()
}

// ---------------------------------------------------------------------
// 4. Weak: downgrade / clone / drop / upgrade
// ---------------------------------------------------------------------

/// Downgrading a strong owner to a non-owning `Weak` handle. EXPECTED:
/// increments the weak count without affecting the strong count or
/// extending the pointee's lifetime. Its release is implicit and therefore
/// absent from today's generated Lean.
#[verify::stateful_lifetimes]
pub fn arc_downgrade_to_weak(value: i32) -> i32 {
    let a = Arc::new(value);
    let _w = a.downgrade();
    *a.get()
}

/// Cloning a `Weak` handle independently of the strong owner it was
/// downgraded from. EXPECTED: weak count 1 -> 2; strong count unaffected.
#[verify::stateful_lifetimes]
pub fn weak_clone_independent(value: i32) {
    let a = Arc::new(value);
    let w1 = a.downgrade();
    let w2 = w1.clone_weak();
    drop(w1);
    drop(w2);
    drop(a);
}

/// Dropping a `Weak` handle has no effect on the strong owner: `a` is
/// still readable afterwards. EXPECTED: weak count 1 -> 0; strong count
/// untouched.
#[verify::stateful_lifetimes]
pub fn weak_drop_no_effect_on_strong(value: i32) -> i32 {
    let a = Arc::new(value);
    let w = a.downgrade();
    drop(w);
    *a.get()
}

/// A dangling `Weak::new()` owns no control block and can never upgrade.
#[verify::stateful_lifetimes]
pub fn dangling_weak_never_upgrades() -> bool {
    let w: Weak<i32> = Weak::new();
    w.upgrade().is_some()
}

/// Upgrading a `Weak` while a strong owner is still alive. EXPECTED:
/// `upgrade` succeeds (`Some`) and yields a *new* strong owner distinct
/// from `a` (strong count would go 1 -> 2).
#[verify::stateful_lifetimes]
pub fn weak_upgrade_while_strong_alive(value: i32) -> bool {
    let a = Arc::new(value);
    let w = a.downgrade();
    let upgraded = w.upgrade();
    upgraded.is_some()
}

/// Upgrading a `Weak` after every strong owner has already been dropped.
/// EXPECTED: `upgrade` observes strong count 0 and returns `None` -- the
/// "last strong owner already gone" event this future feature must
/// distinguish from the live case above.
#[verify::stateful_lifetimes]
pub fn weak_upgrade_after_strong_dropped(value: i32) -> bool {
    let a = Arc::new(value);
    let w = a.downgrade();
    drop(a);
    let upgraded = w.upgrade();
    upgraded.is_some()
}

/// Upgrading the *same* `Weak` handle twice, straddling the point where
/// the *last* of several strong owners is dropped. EXPECTED: generalizing
/// `weak_upgrade_while_strong_alive` / `weak_upgrade_after_strong_dropped`
/// above to multiple strong owners: the first `upgrade` (while `b` is
/// still alive) must observe strong count > 0 and return `Some`; the
/// second `upgrade` (after both `a` and `b` have been dropped) must
/// observe strong count 0 and return `None`. The second observation uses a
/// cloned weak handle so structural CSE cannot replace it with the first.
#[verify::stateful_lifetimes]
pub fn weak_upgrade_before_and_after_last_owner_dropped(value: i32) -> (bool, bool) {
    let a = Arc::new(value);
    let b = a.clone_arc();
    let w = a.downgrade();
    let w_after = w.clone_weak();
    drop(a);
    let before_last = w.upgrade().is_some();
    drop(b);
    let after_last = w_after.upgrade().is_some();
    (before_last, after_last)
}

/// Implicit-scope counterpart of `weak_upgrade_after_strong_dropped`.
/// EXPECTED: the block-end drop of `a` happens before `upgrade`, so the
/// result is `None`. CURRENT: implicit drop glue is absent, making this an
/// explicit regression target for the future drop reconstruction.
#[verify::stateful_lifetimes]
pub fn weak_upgrade_after_owner_scope_exit(value: i32) -> bool {
    let w = {
        let a = Arc::new(value);
        a.downgrade()
    };
    w.upgrade().is_some()
}

// ---------------------------------------------------------------------
// 5. Directly observing strong_count / weak_count
// ---------------------------------------------------------------------

/// Directly observing `strong_count` before and after a `clone_arc`/`drop`
/// pair. EXPECTED: the two `strong_count` observations straddling
/// `clone_arc` should (once implemented) be constrained to differ by
/// exactly one. The second observation uses clone `b` as receiver, avoiding
/// current structural CSE while observing the same allocation.
#[verify::stateful_lifetimes]
pub fn arc_strong_count_across_clone_and_drop(value: i32) -> (usize, usize) {
    let a = Arc::new(value);
    let before = a.strong_count();
    let b = a.clone_arc();
    let after = b.strong_count();
    drop(b);
    (before, after)
}

/// Directly observing `weak_count` after a `downgrade`. EXPECTED:
/// symmetric to `strong_count`, tracked by the same future stateful
/// refcount events.
#[verify::stateful_lifetimes]
pub fn weak_count_after_downgrade(value: i32) -> usize {
    let a = Arc::new(value);
    let _w = a.downgrade();
    a.weak_count()
}

// ---------------------------------------------------------------------
// 6. Clone / drop around branches
// ---------------------------------------------------------------------

/// A strong owner is conditionally cloned, but the extra clone (if any)
/// and the original are always both released by the end of the function.
/// EXPECTED: each branch must independently balance its own "owner
/// created" / "owner released" events; the two branches are not required
/// to produce the same number of events.
#[verify::stateful_lifetimes]
pub fn clone_in_true_branch_only(value: i32, take_extra: bool) {
    let a = Arc::new(value);
    if take_extra {
        let b = a.clone_arc();
        drop(b);
    }
    drop(a);
}

/// Like `clone_in_true_branch_only`, but the branch is a `match` with
/// more than two arms rather than an `if`. EXPECTED: exactly one arm
/// clones an extra strong owner and releases it immediately; every arm --
/// taken or not -- must still leave `a` itself balanced by the trailing
/// `drop(a)`, regardless of which arm ran.
#[verify::stateful_lifetimes]
pub fn clone_in_one_match_arm_only(value: i32, choice: u8) {
    let a = Arc::new(value);
    match choice {
        0 => {
            let b = a.clone_arc();
            drop(b);
        }
        1 => {
            let _ = a.get();
        }
        _ => {}
    }
    drop(a);
}

/// A strong owner is dropped early in exactly one branch, and left alive
/// (to be dropped implicitly at the end of the function) in the other.
/// EXPECTED: the "owner released" event for `a` occurs at a different
/// program point depending on which branch is taken.
#[verify::stateful_lifetimes]
pub fn drop_in_one_branch_only(value: i32, drop_early: bool) {
    let a = Arc::new(value);
    if drop_early {
        drop(a);
    } else {
        let _ = a.get();
        // `a` is dropped implicitly here instead.
    }
}

// ---------------------------------------------------------------------
// 7. Arc<Lock<T>>: acquire/release ordering through a shared owner
// ---------------------------------------------------------------------

/// Acquiring and releasing a read guard reached through `Arc<Lock<T>>`,
/// the common "shared, lock-protected state" shape. EXPECTED: the guard's
/// acquire/release pair is exactly the stateful-lifetime event pair from
/// `lt-stateful-signatures.rs`, now reached through a shared `Arc` instead
/// of a plain reference.
#[verify::stateful_lifetimes]
pub fn arc_rwlock_read_then_release(value: i32) -> i32 {
    let shared = Arc::new(Lock::new(value));
    let guard = shared.get().read();
    let v = *guard.get();
    guard.release();
    v
}

/// Acquiring and releasing a write guard reached through `Arc<Lock<T>>`,
/// mutating the protected value via `get_mut`. EXPECTED: one setter
/// backward function for the write guard, exactly as in the non-`Arc`
/// case.
#[verify::stateful_lifetimes]
pub fn arc_rwlock_write_then_release(value: i32) {
    let shared = Arc::new(Lock::new(value));
    let mut guard = shared.get().write();
    *guard.get_mut() = 42;
    guard.release();
}

/// Sequential ordering: acquire and release a read guard, then acquire
/// and release a write guard on the same `Arc<Lock<T>>`, one strictly
/// after the other (never overlapping). EXPECTED: two independent
/// acquire/release pairs, in program order, sharing the same underlying
/// `Arc`. The Arc projection is intentionally performed once and reused;
/// this tests lock ordering rather than duplicate-call CSE.
#[verify::stateful_lifetimes]
pub fn arc_rwlock_read_then_write_ordering(value: i32) -> i32 {
    let shared = Arc::new(Lock::new(value));
    let lock = shared.get();
    let read_guard = lock.read();
    let seen = *read_guard.get();
    read_guard.release();
    let mut write_guard = lock.write();
    *write_guard.get_mut() = 42;
    write_guard.release();
    seen
}

// ---------------------------------------------------------------------
// 8. Moved / returned Arc; Weak stored in a struct
// ---------------------------------------------------------------------

/// Plain helper that takes an `Arc` *by value*, consuming (and eventually
/// releasing) it inside its own body.
fn consume_arc(a: Arc<i32>) -> i32 {
    let v = *a.get();
    drop(a);
    v
}

/// Moving a strong owner into a helper function by value. EXPECTED: the
/// move transfers ownership; the "owner released" event happens inside
/// `consume_arc`, not at the call site in this function.
#[verify::stateful_lifetimes]
pub fn arc_moved_into_function(value: i32) -> i32 {
    let a = Arc::new(value);
    consume_arc(a)
}

/// Plain helper that creates and returns a fresh strong owner.
fn produce_arc(value: i32) -> Arc<i32> {
    Arc::new(value)
}

/// A strong owner created inside a helper function and returned to the
/// caller. EXPECTED: the "owner created" event happens inside
/// `produce_arc`; ownership (and the eventual release) belongs to the
/// caller.
#[verify::stateful_lifetimes]
pub fn arc_returned_from_function(value: i32) -> i32 {
    let a = produce_arc(value);
    *a.get()
}

/// A `Weak` handle stored as a struct field, the classic parent
/// back-pointer shape used to avoid reference cycles. The `downgrade` call
/// creates the weak owner; the struct literal only moves it into `Child`.
/// The temporary strong owner returned by `upgrade` is also scope-dropped.
#[verify::stateful_lifetimes]
pub fn weak_stored_in_struct_back_pointer(parent_name: i32) -> bool {
    let parent = Arc::new(Parent { name: parent_name });
    let child = Child {
        parent: parent.downgrade(),
    };
    let still_alive = child.parent.upgrade().is_some();
    drop(child);
    still_alive
}

// ---------------------------------------------------------------------
// 9. Drop ordering: struct field vs. sibling local binding
// ---------------------------------------------------------------------

/// A struct holding a single strong-owner field, used to compare its
/// field's release point against a sibling local binding's below.
pub struct Holder {
    pub owner: Arc<i32>,
}

#[verify::opaque]
fn observe_holder(_holder: &Holder) -> i32 {
    unimplemented!()
}

/// A struct field owner (`holder.owner`) versus a plain local `Arc`
/// binding (`local`) declared immediately afterwards, in the same scope.
/// EXPECTED: ordinary local-binding drop order applies first -- bindings
/// are released in the *reverse* of their declaration order -- so `local`
/// (declared second) is released before `holder` (declared first); only
/// once `holder` itself is released does its `owner` field get released,
/// as part of the struct's own field-drop glue. `observe_holder` keeps the
/// aggregate present in generated Lean; both implicit drops remain
/// aspirational under the current baseline.
#[verify::stateful_lifetimes]
pub fn struct_field_vs_local_drop_order(value_struct: i32, value_local: i32) -> i32 {
    let holder = Holder {
        owner: Arc::new(value_struct),
    };
    let local = Arc::new(value_local);
    observe_holder(&holder) + *local.get()
    // `local` is released first (reverse declaration order), then
    // `holder` -- and with it, its `owner` field -- second.
}

// ---------------------------------------------------------------------
// 10. Reference cycles (documented limitation)
// ---------------------------------------------------------------------

/// A node in a two-node strong-reference cycle: each node's `next`
/// strongly owns the *other* node through `Arc<Lock<CycleNode>>`, the
/// same interior-mutability composition as section 7 above -- a plain
/// `Arc<T>` cannot be mutated after construction, so tying a genuine
/// cycle's knot needs a `Lock` (or equivalent) underneath. The recursive
/// layout is opaque for the same strict-positivity reason as `Node`.
#[verify::opaque]
pub struct CycleNode {
    pub value: i32,
    pub next: Option<Arc<Lock<CycleNode>>>,
}

impl CycleNode {
    #[verify::opaque]
    pub fn new(_value: i32) -> Self {
        unimplemented!()
    }

    #[verify::opaque]
    pub fn set_next(&mut self, _next: Arc<Lock<CycleNode>>) {
        unimplemented!()
    }
}

/// Building a genuine two-node strong reference cycle: `node_a.next`
/// strongly owns `node_b`, and `node_b.next` strongly owns `node_a` right
/// back. EXPECTED / KNOWN LIMITATION: this is the classic `Arc` memory
/// leak -- dropping the two local bindings `node_a` / `node_b` at the end
/// of the function decrements each node's strong count from 2 down to 1,
/// never to 0, so neither pointee is ever actually released. The future
/// stateful-refcount feature is only expected to track count-increment /
/// count-decrement *events*, not whole-graph reachability, so it cannot
/// (and is not expected to) flag this cycle as a leak on its own --
/// detecting it would require a separate, considerably harder
/// liveness/cycle analysis, out of scope for this feature exactly like
/// the `Scope` borrow-tracking limitation documented in
/// `lt-stateful-concurrency-known-failures.rs`.
///
/// CURRENT: the opaque constructor/setter avoid Lean's strict-positivity
/// rejection and preserve both clone/set call sequences, but the pure model
/// does not prove the heap graph actually contains the cycle.
#[verify::stateful_lifetimes]
pub fn arc_two_node_strong_cycle(value_a: i32, value_b: i32) {
    let node_a = Arc::new(Lock::new(CycleNode::new(value_a)));
    let node_b = Arc::new(Lock::new(CycleNode::new(value_b)));
    {
        let mut guard = node_a.get().write();
        guard.get_mut().set_next(node_b.clone_arc());
        guard.release();
    }
    {
        let mut guard = node_b.get().write();
        guard.get_mut().set_next(node_a.clone_arc());
        guard.release();
    }
    // `node_a` and `node_b` now strongly reference each other via `next`;
    // dropping both local owners here leaves each pointee's strong count
    // at 1, not 0 -- the cycle leak described above.
}
