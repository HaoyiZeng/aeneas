//@ [!lean] skip
//@ [lean] subdir=BackendFailures
//@ [lean] aeneas-args=-stateful-lifetimes -eval-drops
#![feature(register_tool)]
#![register_tool(verify)]

use std::marker::PhantomData;

#[verify::opaque]
pub struct Lock<T> {
    marker: PhantomData<T>,
}

#[verify::opaque]
pub struct WriteGuard<'a, T> {
    marker: PhantomData<&'a mut T>,
}

impl<T> Lock<T> {
    #[verify::stateful_lifetimes]
    #[verify::opaque]
    pub fn write(&self) -> WriteGuard<'_, T> {
        unimplemented!()
    }
}

impl<T> WriteGuard<'_, T> {
    #[verify::opaque]
    pub fn get(&self) -> &T {
        unimplemented!()
    }
}

/// Explicit `core::mem::drop` on a guard whose lifetime is stateful.
///
/// DIAGNOSIS (refined; the earlier note in this file was wrong). The problem is
/// not that `drop`'s `Unit` destination is mis-bound. The LLBC declaration is
/// clean — `charon pretty-print` shows `pub fn drop<T>(_1: T)` with no region
/// parameters at all, so Charon propagates nothing here.
///
/// What happens is on the Aeneas side. At the call site `T` is instantiated
/// with `WriteGuard<'a, i32>`, and `'a` is stateful because `Lock::write`
/// declared it so. `region_group_is_stateful` is computed from the
/// *instantiated* signature, so `drop`'s region group inherits the bit and
/// `drop` acquires a stateful backward function with no input and one output
/// (the guard). Being effectful with no input it is then evaluated and merged
/// into the forward result (`back_sg_is_evaluated`), so the call is typed
/// `WriteGuard -> Result WriteGuard` at the call site — while the extracted
/// axiom, generated from the *uninstantiated* declaration where `T` is opaque
/// and carries no region, is `T -> Result Unit`. Hence the ill-typed output.
///
/// Confirmed by two controls: translating this file without
/// `-stateful-lifetimes` is correct, and translating it *with* the flag but
/// with `#[verify::stateful_lifetimes]` removed from `Lock::write` is also
/// correct. Only the combination fails.
///
/// The fix is to make a callee's region group stateful only when the callee's
/// own declared signature marks it, so that a stateful lifetime flowing into a
/// generic callee does not give that callee backward functions its declaration
/// does not have. Lexical MIR guard drops are unaffected and work today.
pub fn explicit_drop(lock: &Lock<i32>) {
    let guard = lock.write();
    let _value = *guard.get();
    drop(guard);
}
