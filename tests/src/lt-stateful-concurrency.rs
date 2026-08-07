//@ [!lean] skip
//! EXPECTED AFTER IMPLEMENTATION:
//! This file complements `lt-stateful-arc.rs` (strong/weak refcount
//! lifecycle) and the guard-acquire/release fixtures in
//! `lt-stateful-signatures.rs`, `lt-stateful-reborrows.rs`,
//! `lt-stateful-wrappers.rs`, `lt-stateful-drop.rs`, and
//! `lt-stateful-control.rs` with a dedicated fixture set for **concurrency
//! events**: spawning and joining workers, closures that capture data (by
//! move) into a worker, sharing an `Arc`/`Lock` with a worker, and the
//! scoped-thread shape that lets a worker *borrow* (rather than own) data
//! from the spawning scope. Once a future ITree "stateful concurrency
//! events" pass is implemented -- generalizing the guard/refcount
//! event-tracking explored in the files above to a genuinely *concurrent*
//! join point -- it is expected to translate:
//!   - `spawn` as opening a fresh, independent worker event stream, whose
//!     *first* event is the (opaque) execution of the spawned closure.
//!   - `JoinHandle::join` as the synchronization point where the spawning
//!     thread's event stream and the worker's event stream are merged back
//!     into one, in program order at the call site (not necessarily in
//!     spawn order -- see `join_order_reversed` below).
//!   - A move-captured value (a `String`, an `Arc` clone, a `Lock` handle,
//!     ...) as transferring its entire prior ownership/release event
//!     history into the worker's event stream at the `spawn` call site.
//!   - A dropped, never-joined `JoinHandle` as leaving its worker's event
//!     stream permanently unsynchronized with the spawning thread (in real
//!     `std::thread`, the worker keeps running detached).
//!   - `FallibleJoinHandle::join`'s `Result` return value (mirroring the
//!     real `std::thread::JoinHandle::join`'s `thread::Result<T>`) as the
//!     shape that must let a worker's *panicked* event stream reach the
//!     joiner as `Err`, without resurrecting or duplicating any release
//!     event the worker performed before panicking.
//!   - `Scope::spawn` (the scoped-thread shape) as requiring the borrowed
//!     data's lifetime to outlive the *scope's own join point* (the
//!     closing `}` of the `scope(...)` call) rather than the ordinary,
//!     purely sequential drop point used elsewhere -- see the dedicated
//!     discussion on `Scope` in `lt-stateful-concurrency-known-failures.rs`
//!     (moved there, see the note below), documented as **known
//!     unsupported / future work** for this feature.
//!
//! CURRENT BASELINE:
//! `#[verify::stateful_lifetimes]` is an inert tool attribute today
//! (registered via `#![register_tool(verify)]` but not yet interpreted by
//! Aeneas). `JoinHandle<T>`, `FallibleJoinHandle<T>`, `Arc<T>`, `Lock<T>`,
//! `ReadGuard`, and `WriteGuard`-shaped values are all `#[verify::opaque]`,
//! so every
//! method call and free function (`spawn`, `spawn_fallible`, `yield_now`,
//! `run_with_callback`, ...) is extracted today as an ordinary opaque
//! call, with no concurrent-event-stream reasoning whatsoever: `spawn` and
//! `join` are just two independent opaque calls, exactly as unrelated as
//! any other pair of opaque calls in `lt-stateful-passes.rs`. Every
//! function in this file is required to be valid, borrow-checked Rust --
//! and, in particular, to compile *without* creating any real OS thread --
//! and is expected to keep translating today exactly as any other
//! opaque-call fixture does; none of the workers below ever actually run
//! (there is no `main`, no `#[verify::test]`, and `spawn` is an
//! `unimplemented!()` stub).
//! Implicit `Drop::drop` glue is not emitted today, so claims about an
//! Arc clone's eventual scope-exit release are aspirational.
//!
//! NOTE: the scoped-thread-shaped API (`Scope<'scope, 'env>`, `Scope::spawn`,
//! and the `scope` free function) and the two fixtures that exercise it
//! (`scoped_spawn_shape`, `scoped_spawn_no_explicit_join`) have been moved
//! to `lt-stateful-concurrency-known-failures.rs`. The `scope` function's
//! `for<'scope> FnOnce(&'scope Scope<'scope, 'env>) -> R` bound is a
//! higher-ranked lifetime constraint relating to the free lifetime `'env`,
//! which currently crashes Aeneas's region-hierarchy computation (see that
//! file's module doc for the exact error). Isolating it there lets the rest
//! of this suite (ordinary, non-scoped spawn/join shapes) keep generating
//! successfully.
#![feature(register_tool)]
#![register_tool(verify)]

use std::marker::PhantomData;

// ---------------------------------------------------------------------
// Opaque spawn / join prelude
// ---------------------------------------------------------------------

/// An opaque handle to a spawned worker, mirroring
/// `std::thread::JoinHandle<T>`.
#[verify::opaque]
pub struct JoinHandle<T> {
    _marker: PhantomData<T>,
}

impl<T> JoinHandle<T> {
    /// Block until the worker finishes and recover its result. EXPECTED:
    /// the join point is where the two concurrent event streams (spawning
    /// thread / worker) are (re)synchronized.
    #[verify::opaque]
    pub fn join(self) -> T {
        unimplemented!()
    }
}

/// An opaque "spawn a worker" entry point, mirroring `std::thread::spawn`.
/// EXPECTED: opens a fresh, independent concurrent event stream; the
/// returned `JoinHandle` carries the eventual join-side synchronization
/// event. Unlike real `std::thread::spawn`, no `Send + 'static` bounds are
/// required here: no real OS thread is ever created, which lets these
/// fixtures also exercise borrowed captures (and the `Scope` shapes in
/// `lt-stateful-concurrency-known-failures.rs`) without tripping over
/// `Send`/`Sync`, an entirely separate
/// (and already well-tested) part of the type system.
#[verify::opaque]
pub fn spawn<F, T>(_f: F) -> JoinHandle<T>
where
    F: FnOnce() -> T,
{
    unimplemented!()
}

/// An opaque handle to a spawned worker that may fail, mirroring the
/// *real* return type of `std::thread::JoinHandle::join`, which is
/// `thread::Result<T> = Result<T, Box<dyn Any + Send + 'static>>` -- a
/// worker that panics is observed by its joiner as `Err`, never as an
/// unwound panic propagating across the join point. Kept as a separate
/// opaque type from `JoinHandle<T>` above (rather than changing `join`'s
/// return type there) so every existing infallible spawn/join fixture
/// keeps its simpler shape; this type exists purely to exercise the
/// "worker panicked" event shape in isolation.
#[verify::opaque]
pub struct FallibleJoinHandle<T> {
    _marker: PhantomData<T>,
}

impl<T> FallibleJoinHandle<T> {
    /// Block until the worker finishes, returning `Err` in place of a
    /// propagated panic. EXPECTED: exactly like `JoinHandle::join`, this
    /// is the resynchronization point between the two event streams --
    /// but the future feature must also account for the worker's event
    /// stream ending in a "panicked" event instead of an ordinary return,
    /// without ever resurrecting or duplicating any release event the
    /// worker already performed before panicking.
    #[verify::opaque]
    pub fn join(self) -> Result<T, ()> {
        unimplemented!()
    }
}

/// A `spawn` variant returning a `FallibleJoinHandle`, mirroring the
/// worker-may-panic shape above.
#[verify::opaque]
pub fn spawn_fallible<F, T>(_f: F) -> FallibleJoinHandle<T>
where
    F: FnOnce() -> T,
{
    unimplemented!()
}

/// An opaque cooperative yield point, mirroring `std::thread::yield_now`.
/// EXPECTED: a pure scheduling hint with no ownership/lifetime effect of
/// its own; it must never itself count as a spawn or join event.
#[verify::opaque]
pub fn yield_now() {}

// ---------------------------------------------------------------------
// Opaque Arc<T> / Lock<T> prelude (self-contained; see `lt-stateful-arc.rs`
// for the full Arc/Weak refcount fixture set -- duplicated here in
// miniature, as every `lt-stateful-*.rs` file duplicates its own
// Lock/Guard prelude, so this file has no cross-file dependency)
// ---------------------------------------------------------------------

/// A minimal opaque, reference-counted strong owner, mirroring
/// `std::sync::Arc`, just enough to exercise "share this with a worker"
/// patterns below.
#[verify::opaque]
pub struct Arc<T> {
    _marker: PhantomData<T>,
}

impl<T> Arc<T> {
    #[verify::opaque]
    pub fn new(_value: T) -> Self {
        unimplemented!()
    }

    #[verify::opaque]
    pub fn get(&self) -> &T {
        unimplemented!()
    }

    #[verify::opaque]
    pub fn clone_arc(&self) -> Self {
        unimplemented!()
    }
}

impl<T> Drop for Arc<T> {
    #[verify::opaque]
    fn drop(&mut self) {
        unimplemented!()
    }
}

/// A minimal opaque lock guarding a `T`, mirroring `std::sync::RwLock`,
/// just enough to exercise "acquire/release around (or inside) a worker"
/// patterns below.
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
// Opaque "concurrent callback" prelude
// ---------------------------------------------------------------------

/// An opaque "run to completion" callback executor, standing in for the
/// completion callback of a future concurrent/async operation (think a
/// channel receiver's continuation, or a completion-port callback).
/// EXPECTED: the callback's invocation is itself a concurrency event,
/// distinct from an ordinary (synchronous) function call.
#[verify::opaque]
pub fn run_with_callback<F, T>(_input: i32, _f: F) -> T
where
    F: FnOnce(i32) -> T,
{
    unimplemented!()
}

// ---------------------------------------------------------------------
// 1. Minimal spawn / join shapes
// ---------------------------------------------------------------------

/// Minimal single spawn/join pair. EXPECTED: one worker event stream,
/// synchronized exactly once at `join`.
#[verify::stateful_lifetimes]
pub fn spawn_and_join_single() -> i32 {
    let handle = spawn(|| 42);
    handle.join()
}

/// Two independent spawns, each joined once, in the order they were
/// spawned. EXPECTED: two independent worker event streams, each with its
/// own join synchronization point.
#[verify::stateful_lifetimes]
pub fn spawn_and_join_two() -> (i32, i32) {
    let h1 = spawn(|| 1);
    let h2 = spawn(|| 2);
    let r1 = h1.join();
    let r2 = h2.join();
    (r1, r2)
}

/// Two independent workers, both joined, whose results are combined by an
/// ordinary arithmetic expression rather than returned as a tuple.
/// EXPECTED: like `spawn_and_join_two`, two independent worker event
/// streams, each synchronized at its own `join`; the combination itself
/// (`*`) is an ordinary pure computation downstream of both join points,
/// exercising the case where a *single* expression depends on more than
/// one worker's result at once.
#[verify::stateful_lifetimes]
pub fn two_workers_combine_results() -> i32 {
    let h1 = spawn(|| 3);
    let h2 = spawn(|| 4);
    h1.join() * h2.join()
}

/// Two spawns joined in the *reverse* order they were spawned. EXPECTED:
/// join order must not be assumed to match spawn order; each `JoinHandle`
/// carries its own independent synchronization point.
#[verify::stateful_lifetimes]
pub fn join_order_reversed() -> (i32, i32) {
    let h1 = spawn(|| 10);
    let h2 = spawn(|| 20);
    let r2 = h2.join();
    let r1 = h1.join();
    (r1, r2)
}

/// A join handle dropped without ever being joined. EXPECTED: an
/// un-joined worker event stream that is never explicitly synchronized
/// (in real `std::thread`, the worker keeps running detached). CURRENT:
/// `JoinHandle` has no `Drop` impl of its own, so this is an ordinary
/// no-op scope-exit drop today.
#[verify::stateful_lifetimes]
pub fn handle_drop_without_join() {
    let handle = spawn(|| 99);
    drop(handle);
}

/// Two handles spawned back-to-back, but only the *first* is dropped
/// (detached) -- after both spawns have already happened, and *before*
/// the second is joined. EXPECTED: detaching `h1` must not affect `h2`'s
/// own independent event stream or its join point; the ordering of the
/// detach event relative to the (already-completed) second spawn event
/// must not matter, only its ordering relative to `h2`'s own join.
#[verify::stateful_lifetimes]
pub fn handle_detach_then_other_handle_joined() -> i32 {
    let h1 = spawn(|| 1);
    let h2 = spawn(|| 2);
    drop(h1);
    h2.join()
}

/// A worker whose (possible) panic is observed at the join point as
/// `Err`, mirroring `std::thread::JoinHandle::join`'s real `Result`
/// return type. EXPECTED: the `match` on `join`'s result is itself an
/// ordinary (non-concurrency) control-flow event -- the concurrency
/// feature's job ends at producing the `Result`, exactly at the
/// resynchronization point.
#[verify::stateful_lifetimes]
pub fn worker_panic_reflected_in_join_result() -> i32 {
    let handle = spawn_fallible(|| 42);
    match handle.join() {
        Ok(v) => v,
        Err(()) => -1,
    }
}

// ---------------------------------------------------------------------
// 2. Closure captures
// ---------------------------------------------------------------------

/// A worker closure that captures its environment *by move* (`String`,
/// `Vec`). EXPECTED: the moved-in data's ownership event history is
/// transferred into the spawned worker's event stream at the `spawn` call
/// site.
#[verify::stateful_lifetimes]
pub fn closure_capture_by_move() -> usize {
    let owned = String::from("payload");
    let items = vec![1, 2, 3];
    let handle = spawn(move || owned.len() + items.len());
    handle.join()
}

/// Shared borrow captured by a worker closure. CURRENT BASELINE: the shared
/// region is erased and `spawn` is an ordinary opaque call. Future
/// concurrency semantics must keep the borrow live until `join`.
#[verify::stateful_lifetimes]
pub fn spawn_capturing_shared_borrow(x: &i32) -> i32 {
    let handle = spawn(|| *x + 1);
    handle.join()
}

// ---------------------------------------------------------------------
// 3. Sharing an Arc / Lock with a worker
// ---------------------------------------------------------------------

/// An `Arc` clone moved into a worker closure, the classic "share state
/// with a spawned worker" pattern. EXPECTED: `clone_arc` increments the
/// strong count *before* the spawn boundary; the clone's eventual release
/// (inside the worker) is part of the worker's own event stream,
/// independent of the original owner `shared`.
#[verify::stateful_lifetimes]
pub fn arc_cloned_into_worker(value: i32) -> i32 {
    let shared = Arc::new(value);
    let worker_owner = shared.clone_arc();
    let handle = spawn(move || *worker_owner.get());
    let result = handle.join();
    let _ = shared.get();
    result
}

/// A `JoinHandle` dropped without joining (as in `handle_drop_without_join`
/// above), but this time the spawned closure moved in an `Arc` clone.
/// EXPECTED: the moved-in clone's release event still happens -- inside
/// the detached worker's own, permanently-unsynchronized event stream --
/// exactly as if the handle had been joined; only the *synchronization*
/// with the spawning thread is missing, never the clone's own eventual
/// release.
#[verify::stateful_lifetimes]
pub fn detached_handle_holds_arc_clone(value: i32) -> i32 {
    let shared = Arc::new(value);
    let worker_owner = shared.clone_arc();
    let handle = spawn(move || *worker_owner.get());
    drop(handle);
    *shared.get()
}

/// A worker capturing a moved-in `Arc` clone that then fails (models a
/// panic), observed by the caller via `FallibleJoinHandle::join`.
/// EXPECTED: the moved-in clone's ownership/release event history is
/// still transferred into the worker's event stream at the
/// `spawn_fallible` call site regardless of whether the worker eventually
/// succeeds or fails; a failed `join` must not resurrect, skip, or
/// duplicate that release.
#[verify::stateful_lifetimes]
pub fn worker_failure_after_arc_capture(value: i32) -> i32 {
    let shared = Arc::new(value);
    let worker_owner = shared.clone_arc();
    let handle = spawn_fallible(move || *worker_owner.get());
    let result = match handle.join() {
        Ok(v) => v,
        Err(()) => -1,
    };
    let _ = shared.get();
    result
}

/// A lock acquired and released *entirely inside* a worker closure.
/// EXPECTED: the acquire/release pair belongs to the worker's own event
/// stream, independent of the spawning thread's events.
#[verify::stateful_lifetimes]
pub fn lock_in_worker(value: i32) -> i32 {
    let shared = Arc::new(Lock::new(value));
    let worker_owner = shared.clone_arc();
    let handle = spawn(move || {
        let guard = worker_owner.get().read();
        let v = *guard.get();
        guard.release();
        v
    });
    handle.join()
}

/// A lock acquired *before* spawning a worker and released *after*
/// joining it, straddling the spawn/join boundary entirely from the
/// spawning thread's side. EXPECTED: the acquire and release are both
/// ordinary (non-worker) events; the future feature must not assume every
/// lock event happens inside a worker.
#[verify::stateful_lifetimes]
pub fn lock_around_spawn_join(value: i32) -> i32 {
    let lock = Lock::new(value);
    let guard = lock.read();
    let handle = spawn(|| 7);
    let worker_result = handle.join();
    let v = *guard.get();
    guard.release();
    v + worker_result
}

/// Write-guard counterpart of `lock_around_spawn_join`. The guard stays
/// live across spawn/join, then generated Lean applies a real `get_mut`
/// backward after the join; the read case has no backward component.
#[verify::stateful_lifetimes]
pub fn write_guard_around_spawn_join(value: i32) -> i32 {
    let lock = Lock::new(value);
    let mut guard = lock.write();
    let handle = spawn(|| 7);
    let worker_result = handle.join();
    *guard.get_mut() += 1;
    let v = *guard.get();
    guard.release();
    v + worker_result
}

/// A read guard itself is moved into the worker and released there. This
/// passing case sharpens the boundary with the known failure where the
/// worker returns a guard back across `join`.
#[verify::stateful_lifetimes]
pub fn worker_owns_read_guard(lock: &Lock<i32>) -> i32 {
    let guard = lock.read();
    let handle = spawn(move || {
        let value = *guard.get();
        guard.release();
        value
    });
    handle.join()
}

/// Two independent `Arc<Lock<T>>` pairs, each acquired and released
/// inside its own worker. EXPECTED: two fully independent (worker, lock)
/// event streams; nothing about the future concurrency-events feature
/// should require them to be interleaved or ordered relative to each
/// other.
#[verify::stateful_lifetimes]
pub fn two_locks_two_workers_independent(a: i32, b: i32) -> (i32, i32) {
    let lock_a = Arc::new(Lock::new(a));
    let lock_b = Arc::new(Lock::new(b));
    let owner_a = lock_a.clone_arc();
    let owner_b = lock_b.clone_arc();
    let ha = spawn(move || {
        let guard = owner_a.get().read();
        let v = *guard.get();
        guard.release();
        v
    });
    let hb = spawn(move || {
        let guard = owner_b.get().read();
        let v = *guard.get();
        guard.release();
        v
    });
    (ha.join(), hb.join())
}

// ---------------------------------------------------------------------
// 4. Collections of handles, nesting, yielding, and ownership transfer
// ---------------------------------------------------------------------

/// Several worker handles collected into a `Vec`, all joined via a loop.
/// EXPECTED: N independent worker event streams, each synchronized at its
/// own `join`, aggregated by ordinary control flow (a loop), not by the
/// concurrency feature itself.
#[verify::stateful_lifetimes]
pub fn multiple_handles_collected_in_vec(values: Vec<i32>) -> i32 {
    let mut handles: Vec<JoinHandle<i32>> = Vec::new();
    for v in values {
        handles.push(spawn(move || v * 2));
    }
    let mut total = 0;
    for handle in handles {
        total += handle.join();
    }
    total
}

/// Several worker handles collected into a `Vec` and *never* joined --
/// contrasted with `multiple_handles_collected_in_vec` above, which joins
/// every element via a loop. EXPECTED: the container's own `Drop` glue
/// drops every `JoinHandle` element in turn, leaving every one of the N
/// worker event streams permanently detached and unsynchronized, exactly
/// like `handle_drop_without_join` above but for a whole collection at
/// once.
#[verify::stateful_lifetimes]
pub fn container_of_handles_dropped_unjoined(values: Vec<i32>) {
    let mut handles: Vec<JoinHandle<i32>> = Vec::new();
    for v in values {
        handles.push(spawn(move || v * 2));
    }
    // `handles` (and every `JoinHandle` it contains) is dropped here,
    // detaching every worker without ever joining it.
}

/// The value returned by `join` is immediately used in further
/// computation. EXPECTED: `join`'s result behaves as an ordinary pure
/// value once synchronization has happened; no special-casing is expected
/// downstream of the join point.
#[verify::stateful_lifetimes]
pub fn join_result_used_in_computation() -> i32 {
    let handle = spawn(|| 5);
    let value = handle.join();
    value * value + 1
}

/// A worker whose closure itself spawns (and joins) a second, nested
/// worker before returning. EXPECTED: two nested worker event streams,
/// the inner one fully synchronized before the outer worker's own result
/// is produced.
#[verify::stateful_lifetimes]
pub fn nested_spawn_inside_worker() -> i32 {
    let outer = spawn(|| {
        let inner = spawn(|| 3);
        inner.join() + 1
    });
    outer.join()
}

/// A cooperative yield point placed between spawning and joining.
/// EXPECTED: `yield_now` is a no-op with respect to ownership/lifetime
/// events; it only affects scheduling, never the spawn/join event pair.
#[verify::stateful_lifetimes]
pub fn spawn_then_yield_then_join() -> i32 {
    let handle = spawn(|| 11);
    yield_now();
    handle.join()
}

/// Plain helper that takes ownership of a `JoinHandle` and joins it,
/// applying a further transformation to the result.
fn join_and_double(handle: JoinHandle<i32>) -> i32 {
    handle.join() * 2
}

/// A `JoinHandle` moved into a helper function by value, rather than
/// joined directly at the spawn site. EXPECTED: ownership of the pending
/// join synchronization event is transferred along with the handle; the
/// actual `join` still happens exactly once, inside the helper.
#[verify::stateful_lifetimes]
pub fn join_handle_moved_into_helper() -> i32 {
    let handle = spawn(|| 21);
    join_and_double(handle)
}

/// A first handle is spawned and dropped (unjoined) before a second,
/// unrelated worker is spawned and joined. EXPECTED: the dropped handle's
/// worker event stream is never synchronized; the second worker is an
/// entirely independent event stream with its own join.
#[verify::stateful_lifetimes]
pub fn drop_handle_early_then_spawn_more() -> i32 {
    let first = spawn(|| 1);
    drop(first);
    let second = spawn(|| 2);
    second.join()
}

// ---------------------------------------------------------------------
// 5. Concurrent callback patterns
// ---------------------------------------------------------------------

/// A single callback invoked once by the (opaque) executor. EXPECTED: one
/// callback-invocation event, carrying `input` in and its result out.
#[verify::stateful_lifetimes]
pub fn concurrent_callback_single(input: i32) -> i32 {
    run_with_callback(input, |x| x + 1)
}

/// A callback that itself schedules (and immediately awaits, via a
/// second opaque call) a follow-up callback -- a minimal "completion
/// chaining" shape. EXPECTED: two sequential, nested callback-invocation
/// events, the inner one fully resolved before the outer one returns.
#[verify::stateful_lifetimes]
pub fn concurrent_callback_chained(input: i32) -> i32 {
    run_with_callback(input, |x| run_with_callback(x, |y| y * 2))
}
