//@ [!lean] skip
//! # Stateful lock/guard lifetime fixtures — FAILURE-PATH variants
//!
//! This file complements `lt-stateful-returns.rs` by stress-testing failure
//! sources around the same opaque lock/guard vocabulary: arithmetic
//! overflow candidates (plain, `checked_*`, and `wrapping_*`),
//! division/remainder by zero, `assert!`/`debug_assert!`/`panic!`,
//! out-of-bounds indexing (array, slice, and `Option::unwrap`), a fallible
//! opaque external call (including one that borrows a live `&Guard`),
//! `Result`/`Option` error paths that overflow or panic on their own
//! success value, `?`-based (as opposed to `panic!`-based) error
//! propagation both before and after a guard is acquired, error-type
//! conversion via `From`/`?`, and — specific to the lock/guard vocabulary —
//! failures that occur *before* a guard is ever acquired, failures that
//! occur *after* a guard is acquired (with no `Drop` glue to release it,
//! since `Guard` is opaque), and failures that occur while multiple guards
//! are nested in scope.
//!
//! Unwind recovery remains isolated in `lt-stateful-unwind.rs`. Process
//! abort is included here because Aeneas does translate it: `abort` has
//! result type `Never`, followed by `fail panic`. This intentionally records
//! that today's pure model collapses abort and panic into the same failure.
//!
//! As with the returns file, `Lock` / `Guard<'_>` are `#[verify::opaque]`
//! and carry no `Drop` glue, and `#[verify::stateful_lifetimes]` (used
//! below as a bare marker, with no arguments) is **tentative /
//! exploratory**: it is inert today (accepted only because `verify` is a
//! registered tool), reserved for a possible future Aeneas pass that would
//! reason about held-state values across fallible code. "Inert" does not
//! mean silent, though: Charon's attribute parser (`parse_special_attr` in
//! `translate_meta.rs`) actively inspects every `verify::*` attribute, and
//! `stateful_lifetimes` is not one of the names it special-cases (only
//! `opaque`, `exclude`, `transparent`, `rename`, `variants_prefix`,
//! `variants_suffix`, `start_from`, and `test` are) — so it falls through
//! to the `_ => None` arm, which turns into an `Unrecognized attribute`
//! error that `register_error!` reports at `Level::WARNING`. Today, Charon
//! emits one such (non-fatal) warning per annotated item in this file.
//!
//! ## EXPECTED
//! Rust-level failure sources (`panic!`, `assert!`, `debug_assert!`,
//! integer overflow, out-of-bounds indexing, division/remainder by zero,
//! `Option::unwrap`) should all translate to the Lean `fail` case of the
//! `Result` monad, per the `aeneas-lean-core` skill file. A failing opaque
//! external call should likewise surface as an ordinary `Result`-typed
//! outcome that the caller can propagate with `?`.
//!
//! **`Err`/`None` are not `fail`.** A Rust function returning
//! `Result<T, E>` (or `Option<T>`) that takes its `Err`/`None` path is
//! *not* the same event as an Aeneas `fail`. The Rust-level `Result<T, E>`
//! translates to a distinct two-constructor Lean inductive
//! (`core.result.Result T E`, with `Ok`/`Err`), wrapped *inside* the outer
//! Aeneas effect monad (`Result` in the Lean backend sense: `ok`/`fail`/
//! `div`). Constructing `Err(e)` — whether directly or via early-return
//! through `?` — produces `ok (core.result.Result.Err e)`: an entirely
//! ordinary, *successful* outcome of the outer effect monad that happens to
//! carry a Rust-level error value. `Result::?`'s desugaring (through the
//! `core::ops::Try` trait — schematically
//! `core.result.Result.Insts.CoreOpsTry.branch` then `...from_residual` on
//! early exit) never leaves the outer `ok` case either. A genuine Aeneas
//! `fail` only arises from things this translation itself cannot represent
//! as a value: a panic, an overflow, an out-of-bounds access, a division by
//! zero — i.e. exactly the *other* fixtures in this file. See
//! [`call_fallible_external`] and the `?`-before/after-acquire pair below
//! for concrete illustrations of this distinction.
//!
//! ## CURRENT
//! Most functions in this file exercise failure patterns that already have
//! established translations elsewhere in the test suite (see
//! `overflowing-ops.rs`, `assert-cfg.rs`, `array_slice_index.rs`) and are
//! expected to translate cleanly — the whole file is expected to keep
//! translating; nothing here warrants a file-level `known-failure` marker.
//!
//! Guard-specific hazards (documented per-function below): a guard
//! acquired just before a fallible operation is **never released** on the
//! failing path, because `Guard` is opaque and therefore has no `Drop`
//! glue. In a real, non-opaque `MutexGuard`-based program this would be a
//! genuine resource leak (or, with a real `Drop` impl, an implicit release
//! Aeneas would still need to model); worth keeping in mind when writing
//! specs for functions that hold guards across fallible operations.

#![feature(register_tool)]
#![register_tool(verify)]

// ---------------------------------------------------------------------------
// Opaque lock/guard vocabulary (mirrors lt-stateful-returns.rs; duplicated
// here so this file stays self-contained).
// ---------------------------------------------------------------------------

/// Opaque handle representing exclusive access to some resource.
#[verify::opaque]
pub struct Lock {
    _priv: u32,
}

/// Opaque RAII-shaped guard borrowing from a `Lock`; no `Drop` glue.
///
#[verify::opaque]
pub struct Guard<'a> {
    lock: &'a Lock,
}

#[verify::stateful_lifetimes]
#[verify::opaque]
pub fn acquire(l: &Lock) -> Guard<'_> {
    unimplemented!()
}

#[verify::stateful_lifetimes]
#[verify::opaque]
pub fn release(g: Guard<'_>) {
    unimplemented!()
}

/// Opaque helper that consumes a guard by value and returns a scalar.
#[verify::opaque]
pub fn consume_guard(g: Guard<'_>) -> u32 {
    unimplemented!()
}

// ---------------------------------------------------------------------------
// Arithmetic overflow candidates.
// ---------------------------------------------------------------------------

/// EXPECTED: overflowing `u32` addition fails (Lean `fail`) rather than
/// wrapping, matching Rust's debug-mode overflow-checked semantics.
pub fn overflow_add_candidate(x: u32, y: u32) -> u32 {
    x + y
}

/// EXPECTED: overflowing `u16` multiplication fails analogously.
pub fn overflow_mul_candidate(x: u16, y: u16) -> u16 {
    x * y
}

/// EXPECTED: underflowing `u32` subtraction fails.
pub fn underflow_sub_candidate(x: u32, y: u32) -> u32 {
    x - y
}

// ---------------------------------------------------------------------------
// The checked / wrapping / overflow trio: three different Rust-level
// answers to "what happens on overflow?", stress-testing that Aeneas keeps
// them distinct rather than collapsing them all to `fail`.
// ---------------------------------------------------------------------------

/// EXPECTED: same as [`overflow_add_candidate`] — plain `+` fails (Lean
/// `fail`) on overflow. Included here purely to sit next to its
/// `checked_add`/`wrapping_add` counterparts below for direct comparison.
pub fn overflow_trio_plain_add(x: u32, y: u32) -> u32 {
    x + y
}

/// EXPECTED: `checked_add` never fails at the Aeneas level — overflow is
/// represented as an ordinary `Option::None` *value*
/// (`ok (Option.none)`), exactly analogous to how `Result::Err` is not a
/// `fail` (see module docs above). The Aeneas-level `fail` case simply
/// does not arise here at all.
pub fn overflow_trio_checked_add(x: u32, y: u32) -> Option<u32> {
    x.checked_add(y)
}

/// EXPECTED: `wrapping_add` never fails and never produces an `Option` —
/// it is a total, pure scalar operation (modular addition). No monadic
/// `fail` and no `core.result.Result`/`Option` wrapping at all: just an
/// ordinary value-returning function in the `Result` monad's `ok` case.
pub fn overflow_trio_wrapping_add(x: u32, y: u32) -> u32 {
    x.wrapping_add(y)
}

// ---------------------------------------------------------------------------
// Division / remainder by zero.
// ---------------------------------------------------------------------------

/// EXPECTED: division by zero fails.
pub fn div_by_zero_candidate(x: u32, y: u32) -> u32 {
    x / y
}

/// EXPECTED: remainder by zero fails.
pub fn rem_by_zero_candidate(x: u32, y: u32) -> u32 {
    x % y
}

// ---------------------------------------------------------------------------
// assert! / debug_assert! / panic!.
// ---------------------------------------------------------------------------

/// EXPECTED: a failing `assert!` translates to `fail`, as in
/// `assert-cfg.rs`.
pub fn assert_candidate(x: u32) -> u32 {
    assert!(x > 0);
    x - 1
}

/// EXPECTED: `debug_assert!` translates the same way as `assert!` — both
/// lower to the same `Assert` MIR terminator in a debug build, which is
/// how these fixtures are always compiled/extracted (see `assert-cfg.rs`
/// for the `cfg(debug_assertions)`-sensitive variant of this same point).
/// Unlike `assert!`, this check is compiled out entirely in a release
/// build, but that distinction is invisible at the MIR level Aeneas
/// consumes when debug assertions are enabled.
pub fn debug_assert_candidate(x: u32) -> u32 {
    debug_assert!(x > 0);
    x - 1
}

/// EXPECTED: an explicit `panic!` on the failing branch translates to
/// `fail`.
pub fn panic_candidate(flag: bool) -> u32 {
    if flag {
        panic!("explicit panic")
    } else {
        0
    }
}

/// CURRENT BASELINE: `std::process::abort : Result Never`; the impossible
/// continuation is followed by `fail panic`. The model does not distinguish
/// non-unwinding process termination from panic.
pub fn abort_candidate(x: u32) -> u32 {
    if x == 0 {
        std::process::abort();
    }
    x - 1
}

// ---------------------------------------------------------------------------
// Bounds indexing.
// ---------------------------------------------------------------------------

/// EXPECTED: out-of-bounds fixed-size array indexing fails, as in
/// `array_slice_index.rs`.
pub fn index_out_of_bounds_candidate(a: &[u32; 4], i: usize) -> u32 {
    a[i]
}

/// EXPECTED: out-of-bounds slice indexing fails analogously.
pub fn slice_index_candidate(s: &[u32], i: usize) -> u32 {
    s[i]
}

/// EXPECTED: `Option::unwrap` on a `None` produced by an out-of-range
/// `get` fails — a second, `Option`-mediated route to the same
/// out-of-bounds hazard as the two functions above.
pub fn get_unwrap_candidate(s: &[u32], i: usize) -> u32 {
    *s.get(i).unwrap()
}

/// EXPECTED: **`Err`-to-panic**. Unlike [`call_fallible_external`] below
/// (which propagates the `Err` value via `?`, staying in the outer `ok`
/// case the whole way — see module docs above), `.unwrap()` on a `Result`
/// converts that ordinary `Err` *value* into a genuine Aeneas `fail`: this
/// is the one place in this file where an `Err` and a `fail` are directly
/// connected, and the connection is exactly `Result::unwrap`, not `?`.
pub fn err_to_panic_candidate(x: u32) -> u32 {
    let r: Result<u32, u32> = if x > 0 { Ok(x) } else { Err(0) };
    r.unwrap()
}

// ---------------------------------------------------------------------------
// `Result`/`Option` success paths that themselves overflow.
// ---------------------------------------------------------------------------

/// EXPECTED: **`Err` and overflow, distinct hazards in the same function**.
/// Taking the `Err` branch is an ordinary `ok (core.result.Result.Err ...)`
/// value (see module docs above) — it never fails. Taking the `Ok` branch
/// instead runs a plain overflow-checked addition, which *can* produce a
/// genuine Aeneas `fail`. The two hazards are independent: the `Err` path
/// never fails, and the `Ok` path may fail purely due to the addition,
/// with no interaction between the two.
pub fn err_or_overflow_candidate(x: u32, y: u32, fail_early: bool) -> Result<u32, u32> {
    if fail_early {
        Err(0xBAD)
    } else {
        Ok(x + y)
    }
}

/// EXPECTED: **`None` and overflow, the `Option` analogue of
/// [`err_or_overflow_candidate`]**. Taking the `None` branch is an ordinary
/// `ok (Option.none)` value, never a `fail`; taking the `Some` branch runs
/// an overflow-checked multiplication that can genuinely `fail`.
pub fn none_or_overflow_candidate(x: u16, y: u16, absent: bool) -> Option<u16> {
    if absent {
        None
    } else {
        Some(x * y)
    }
}

// ---------------------------------------------------------------------------
// Opaque fallible external call.
// ---------------------------------------------------------------------------

/// Opaque external call that may fail; Aeneas has no visibility into why or
/// when, only that its return type is `Result`.
#[verify::opaque]
pub fn fallible_external_call(x: u32) -> Result<u32, u32> {
    unimplemented!()
}

/// EXPECTED: `fallible_external_call`'s `Err` path (whatever it does
/// internally — the callee is opaque) is, at the Aeneas level, an ordinary
/// `ok (core.result.Result.Err e)` value returned by the opaque call, *not*
/// a monadic `fail` (see module docs above: `Err` is not `fail`). The `?`
/// here desugars via `core::ops::Try` exactly as in
/// `call_acquire_with_status` in `lt-stateful-returns.rs`: it inspects the
/// value and, on the `Err` path, returns
/// `ok (core.result.Result.Err e)` from `call_fallible_external` itself —
/// still squarely within the outer `ok` case the whole way through. A
/// genuine Aeneas `fail` would only occur here if `fallible_external_call`
/// itself panicked or diverged internally, which this opaque signature
/// gives Aeneas no way to see or rule out.
pub fn call_fallible_external(x: u32) -> Result<u32, u32> {
    let y = fallible_external_call(x)?;
    Ok(y + 1)
}

/// Opaque external call that may fail while also inspecting a live guard
/// via a shared borrow — combines the "opaque fallible call" hazard above
/// with the guard vocabulary: the guard is never consumed by this call, so
/// it remains live (and un-released) both on the `Ok` and the `Err` path.
#[verify::opaque]
pub fn fallible_external_call_with_guard(g: &Guard<'_>, x: u32) -> Result<u32, u32> {
    unimplemented!()
}

/// EXPECTED: same `Err`-is-not-`fail` shape as [`call_fallible_external`],
/// but with a `&Guard` argument threaded into the opaque call. On both the
/// `Ok` and the `Err` path, `g` is still live and un-released when this
/// function returns — the `Err` path is not special-cased with respect to
/// the guard, since (as always) it is not a `fail`.
pub fn call_fallible_external_with_guard(lock: &Lock, x: u32) -> Result<u32, u32> {
    let g = acquire(lock);
    let y = fallible_external_call_with_guard(&g, x)?;
    Ok(y + 1)
}

// ---------------------------------------------------------------------------
// Error-type conversion via `From`/`?`.
// ---------------------------------------------------------------------------

/// A small error type distinct from the `u32` error codes used elsewhere
/// in this file, so that [`call_fallible_external_via_from`] below
/// exercises a genuine `From`-mediated conversion rather than an identity
/// one.
#[derive(Debug)]
pub struct WrappedError(u32);

impl From<u32> for WrappedError {
    fn from(e: u32) -> Self {
        WrappedError(e)
    }
}

/// EXPECTED: **`From` conversion**. `?` on `fallible_external_call`'s
/// `Result<u32, u32>` inside a function returning `Result<u32,
/// WrappedError>` desugars through `core::ops::Try`'s `from_residual`,
/// which — unlike the identity-error-type case in
/// [`call_fallible_external`] — additionally invokes
/// `WrappedError::from` (the translation of `#[verify::opaque]`-free,
/// ordinary user code) to convert the `u32` error into a `WrappedError`
/// before wrapping it in `core.result.Result.Err`. As always, this whole
/// conversion happens on the `ok` side of the outer effect monad for this
/// particular infallible identity-like conversion.
pub fn call_fallible_external_via_from(x: u32) -> Result<u32, WrappedError> {
    let y = fallible_external_call(x)?;
    Ok(y + 1)
}

/// A `From` implementation whose conversion can itself overflow. This is
/// a second route from an ordinary Rust `Err` value to an Aeneas `fail`:
/// `from_residual` invokes user code, and that user code may fail.
#[derive(Debug)]
pub struct ScaledError(u32);

impl From<u32> for ScaledError {
    fn from(e: u32) -> Self {
        ScaledError(e * 1_000_000)
    }
}

/// EXPECTED: the Rust `Err` path invokes the overflow-checking
/// `ScaledError::from`, so conversion itself may produce Aeneas `fail`.
pub fn call_fallible_external_via_fallible_from(x: u32) -> Result<u32, ScaledError> {
    let y = fallible_external_call(x)?;
    Ok(y)
}

// ---------------------------------------------------------------------------
// Fail *before* acquiring a guard vs fail *after* acquiring one.
// ---------------------------------------------------------------------------

/// Hazard: the fallible operation (division) runs *before* the lock is
/// ever acquired, so a failure here means the guard is never created at
/// all — the simplest, least surprising case.
///
/// The division's quotient is bound to a *named* (if underscore-prefixed)
/// local, `_quotient`, rather than the bare wildcard pattern `let _ = ...`.
/// This matters for guard-shaped values (`let _ = mutex.lock().unwrap();`
/// is a well-known Rust footgun: the wildcard pattern `_` does not bind the
/// temporary, so a real `Drop`-bearing guard would be released immediately,
/// right there, rather than held for the rest of the statement) but is
/// irrelevant for a plain `Copy` scalar like this quotient, which has no
/// `Drop` glue either way. The two spellings are semantically identical
/// here; `_quotient` is used purely so the intent — "the *value* is
/// discarded, but its potentially-failing *evaluation* is not" — is
/// unambiguous to a reader, and so this fixture cannot be mistaken for an
/// instance of that footgun.
pub fn fail_before_acquire(lock: &Lock, divisor: u32) -> Guard<'_> {
    let _quotient = 10u32 / divisor;
    acquire(lock)
}

/// Hazard: the fallible operation (division) runs *after* the guard `g` has
/// already been acquired. If the division fails, `g` is dropped without
/// ever reaching `consume_guard`/`release` — because `Guard` is opaque and
/// has no `Drop` glue, this is a silent "leak" on the failing path. This is
/// the interesting contrast with [`fail_before_acquire`] above.
pub fn fail_after_acquire(lock: &Lock, divisor: u32) -> u32 {
    let g = acquire(lock);
    let r = 10u32 / divisor;
    let _ = consume_guard(g);
    r
}

// ---------------------------------------------------------------------------
// `?`-based (as opposed to `panic!`-based) failure before/after acquiring a
// guard — the `Result::?` analogue of the `fail_before_acquire` /
// `fail_after_acquire` pair above. Unlike that pair, taking the early-exit
// path here is *not* an Aeneas `fail` at all (see module docs above): it is
// an ordinary `ok (core.result.Result.Err e)` value. The guard-leak hazard
// is therefore different in kind, not just in timing: nothing "fails" on
// this path, yet the guard (when already acquired) is still never
// released, because ordinary `Err`-propagation is just as oblivious to a
// live, un-consumed opaque guard as a genuine panic is.
// ---------------------------------------------------------------------------

/// Hazard: the fallible operation (`?` on the opaque call) runs *before*
/// the lock is ever acquired. On the early-exit path the function returns
/// `ok (core.result.Result.Err e)` and the guard is never created — same
/// shape as [`fail_before_acquire`], but via `?`/`Err` rather than a
/// panicking division.
pub fn try_before_acquire(lock: &Lock, x: u32) -> Result<Guard<'_>, u32> {
    let _y = fallible_external_call(x)?;
    Ok(acquire(lock))
}

/// Hazard: the fallible operation (`?` on the opaque call) runs *after* the
/// guard `g` has already been acquired. On the early-exit path, `g` is
/// dropped without ever reaching `consume_guard`/`release` — exactly like
/// [`fail_after_acquire`], except the exit here is an ordinary `Err` value
/// threaded through `?`, not a monadic `fail`.
pub fn try_after_acquire(lock: &Lock, x: u32) -> Result<u32, u32> {
    let g = acquire(lock);
    let y = fallible_external_call(x)?;
    Ok(consume_guard(g) + y)
}

// ---------------------------------------------------------------------------
// "Fail-then-work" absorption: statements written after a failing operation
// are never reached, because `bind` on a `fail` never invokes its
// continuation.
// ---------------------------------------------------------------------------

/// EXPECTED: once `10u32 / divisor` fails (`divisor == 0`), the subsequent
/// `wrapping_add` and the final `Ok` are never reached — the whole
/// function reduces to that single `fail`, with the "then-work" absorbed.
///
/// **On `bind_fail` (or the lack thereof):** one might expect a simp lemma
/// along the lines of `bind (.fail e) f = .fail e` to witness this
/// absorption directly. `Aeneas/Std/Primitives.lean` does define
/// `Result.fail e := Result.vis (.fail e) PEmpty.elim`, and indeed sketches
/// exactly such a lemma — but it is left **commented out**:
/// ```text
/// -- @[simp] theorem bind_fail (x : Error) (f : α → Result β) : bind (.fail x) f = .fail x :=
/// --   by simp [bind, vis]
/// --      apply congrArg
/// --      funext x
/// --      contradiction
/// ```
/// There is no *definitional* `bind_fail` lemma in the library. Instead,
/// `Result.fail` itself carries `@[simp]`, so `simp` first unfolds
/// `Result.fail e` to `Result.vis (.fail e) PEmpty.elim`, and the existing
/// `bind_vis` lemma (`bind (.vis eff k) f = .vis eff (fun x => bind (k x)
/// f)`) then applies generically — reaching the same normal form as a
/// hypothetical `bind_fail` would, but through `Result.vis`'s eliminator
/// rather than a single direct rewrite. Proofs that need "once we fail,
/// everything downstream is skipped" reasoning about this function should
/// go through that unfolding (or `Result.cases` / `WP.spec_bind`), not
/// expect a `bind_fail` lemma to exist by that name.
pub fn fail_then_work_absorbed(divisor: u32) -> u32 {
    let q = 10u32 / divisor;
    let doubled = q.wrapping_add(q);
    doubled
}

// ---------------------------------------------------------------------------
// Failure inside nested guard scopes.
// ---------------------------------------------------------------------------

/// Hazard: an out-of-bounds index failure occurs while *two* guards
/// (`g_outer` and `g_inner`) are simultaneously held. On the failing path
/// neither guard ever reaches `consume_guard`/`release`.
pub fn nested_guard_scope_failure(
    outer_lock: &Lock,
    inner_lock: &Lock,
    i: usize,
    arr: &[u32; 4],
) -> u32 {
    let g_outer = acquire(outer_lock);
    let v = {
        let g_inner = acquire(inner_lock);
        let x = arr[i];
        let _ = consume_guard(g_inner);
        x
    };
    let _ = consume_guard(g_outer);
    v
}

// ---------------------------------------------------------------------------
// Unwind recovery (`catch_unwind`) is isolated in `lt-stateful-unwind.rs`
// because it does not translate. Process abort remains above as a normal
// baseline fixture because Aeneas models it as `Result Never` followed by
// `fail panic`.
// ---------------------------------------------------------------------------
