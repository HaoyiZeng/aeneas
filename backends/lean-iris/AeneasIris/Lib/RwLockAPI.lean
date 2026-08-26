import AeneasIris.Tactics.Core
import AeneasIris.AtomicWpi
import Iris.BI.Lib.Atomic

/-! # The `RwLock` interface -/

namespace AeneasIris

open Iris BI Aeneas.Data.Coinductive
open AeneasIris.AtomicWpi
open Aeneas.Std (Loc)

/-- The abstract state of a lock: free, `n + 1` readers, or one writer. -/
inductive LockState
  | free
  | read (n : Nat)
  | write
deriving DecidableEq, Repr

def LockState.word : LockState → Int
  | .free => 0
  | .read n => (n : Int) + 1
  | .write => -1

theorem LockState.word_injective :
    Function.Injective LockState.word := by
  intro a b h
  cases a <;> cases b <;> simp_all [AeneasIris.LockState.word] <;> grind

/-! ## The carriers

Declared here rather than in an implementation, for the reason `ArcAPI` gives:
a client type that recurses through one needs an inductive head at the recursive
occurrence, and the kernel's positivity check will accept neither an `abbrev`
alias nor a field of the class.

`T` is phantom in all three: a lock is two locations, a guard is a lock. -/

/-- Model of `my_std::RwLock<T>`. -/
structure RwLock (T : Type) where
  state : Loc
  data : Loc
deriving DecidableEq, Repr

/-- Model of `my_std::RwLockReadGuard<'_, T>`. -/
structure ReadGuard (T : Type) where
  lock : RwLock T
deriving DecidableEq, Repr

/-- Model of `my_std::RwLockWriteGuard<'_, T>`. Distinct from `ReadGuard`. -/
structure WriteGuard (T : Type) where
  lock : RwLock T
deriving DecidableEq, Repr

/-- The guard a successful acquire on `lk` hands back. -/
def mkReadGuard {T : Type} (lk : RwLock T) : ReadGuard T := ⟨lk⟩

def mkWriteGuard {T : Type} (lk : RwLock T) : WriteGuard T := ⟨lk⟩

section Interface

variable {hlc : Iris.HasLC}

/-- A reader/writer lock over `T`, as a menu of operations, three abstract
predicates, and the laws relating them.

Generic in the effect row `E`, the handler `Hd` and the `Mode`, so a client
programs against the interface at whatever language it is itself written in.

The carriers are not fields: `RwLock`, `ReadGuard` and `WriteGuard` are declared
above, and every implementation uses those.  What an implementation is free to
choose is the protocol -- the ghost state, and where the interference points
fall -- not the shape of the lock.  Instance search therefore runs on `GF`, `Hd`
and `m` alone, which is also what lets `new` -- whose result type is the lock --
elaborate without an annotation. -/
class RwLockAPI (GF : BundledGFunctors) [Iris.InvGS_gen hlc GF]
    {E : Effect.{1}} (Hd : Handler E GF) (m : Mode) where
  new {T : Type} : T → ITree E (RwLock T)
  drop {T : Type} : RwLock T → ITree E Unit
  try_read {T : Type} :
    RwLock T → ITree E (Option (ReadGuard T × (ReadGuard T → ITree E Unit)))
  try_write {T : Type} :
    RwLock T → ITree E (Option (WriteGuard T × (WriteGuard T → ITree E Unit)))
  read {T : Type} :
    RwLock T → ITree E (ReadGuard T × (ReadGuard T → ITree E Unit))
  write {T : Type} :
    RwLock T → ITree E (WriteGuard T × (WriteGuard T → ITree E Unit))
  read_deref {T : Type} : ReadGuard T → ITree E T
  write_deref {T : Type} : WriteGuard T → ITree E T
  /-- The second backward function ends the borrow the guard holds on the lock,
  which `deref_mut` only passes through -- so it returns what it was given, and
  is pure.  Releasing is `drop`'s job, not this one's. -/
  write_deref_mut {T : Type} : WriteGuard T →
    ITree E (T × (T → ITree E (WriteGuard T)) × (WriteGuard T → WriteGuard T))

  /-- The lock itself, at abstract state `s` holding `v`. -/
  isRwLock {T : Type} : GName → RwLock T → LockState → T → IProp GF
  /-- Exclusive access to the contents, held *through* `g`.

  Keyed on the guard, not on the lock, so that a guard is the opaque RAII token
  Rust has it be: a client never names one, it receives one from an acquire and
  spends it on a deref or a release.  Which lock is meant is recovered from the
  ghost name, so no acquire has to relate its result back to the lock. -/
  writeGuard {T : Type} : GName → WriteGuard T → T → IProp GF
  /-- Shared access at client-visible strength `q`, likewise held through `g`. -/
  readGuardFrac {T : Type} : GName → ReadGuard T → Qp → T → IProp GF

  isRwLock_timeless {T : Type} γ (lk : RwLock T) s v : Timeless (isRwLock γ lk s v)
  writeGuard_timeless {T : Type} γ (g : WriteGuard T) v : Timeless (writeGuard γ g v)
  readGuardFrac_timeless {T : Type} γ (g : ReadGuard T) q v :
    Timeless (readGuardFrac γ g q v)

  isRwLock_exclusive {T : Type} γ (lk : RwLock T) s₁ s₂ v₁ v₂ :
    iprop(isRwLock γ lk s₁ v₁ ∗ isRwLock γ lk s₂ v₂) ⊢@{IProp GF} iprop(False)
  readGuardFrac_split {T : Type} γ (g : ReadGuard T) q₁ q₂ v :
    iprop(readGuardFrac γ g (q₁ + q₂) v)
      ⊣⊢ iprop(readGuardFrac γ g q₁ v ∗ readGuardFrac γ g q₂ v)
  /-- Absorb another permit for the same lock into your own guard.

  This is the `←` direction of `readGuardFrac_split`, generalised across guards:
  two permits at one `γ` are for one lock, so their fractions add.  The `→`
  direction does *not* generalise -- handing out a permit at an arbitrary other
  guard would fabricate a claim about a lock one does not hold -- which is why
  this is a separate rule rather than a wider `⊣⊢`.

  Without it a client that parks a fraction in a shared invariant has no way to
  name the guard it will be recombined with, and must either fix a canonical
  guard per lock (over-constraining implementations whose guards are genuinely
  distinct) or break the abstraction. -/
  readGuardFrac_combine {T : Type} γ (g₁ g₂ : ReadGuard T) q₁ q₂ v :
    iprop(readGuardFrac γ g₁ q₁ v ∗ readGuardFrac γ g₂ q₂ v)
      ⊢@{IProp GF} iprop(readGuardFrac γ g₁ (q₁ + q₂) v)
  readGuardFrac_state {T : Type} γ (lk : RwLock T) s (g : ReadGuard T) q v v' :
    iprop(isRwLock γ lk s v ∗ readGuardFrac γ g q v') ⊢@{IProp GF} iprop(⌜∃ n, s = .read n⌝)
  readGuardFrac_agree {T : Type} γ (lk : RwLock T) s (g : ReadGuard T) q v v' :
    iprop(isRwLock γ lk s v ∗ readGuardFrac γ g q v') ⊢@{IProp GF} iprop(⌜v = v'⌝)
  writeGuard_state {T : Type} γ (lk : RwLock T) s (g : WriteGuard T) v v' :
    iprop(isRwLock γ lk s v ∗ writeGuard γ g v') ⊢@{IProp GF} iprop(⌜s = .write⌝)

  new_spec {T : Type} (v : T) (M : CoPset) :
    ⦃ emp ⦄ (new v) @ Hd ; m ; M ⦃ lk, ∃ γ, isRwLock γ lk .free v ⦄

  drop_spec {T : Type} (γ : GName) (lk : RwLock T) (v : T) (M : CoPset) :
    ⦃ isRwLock γ lk .free v ⦄ (drop lk) @ Hd ; m ; M ⦃ r, ⌜r = ()⌝ ⦄

  try_write_spec {T : Type} (γ : GName) (lk : RwLock T) :
    ⊢ ⟪ ∀ s v, isRwLock γ lk s v ⟫ Hd m (try_write lk) @ (∅ : CoPset)
        ⟪ isRwLock γ lk (if s = .free then .write else s) v
        | g rel, RET (if s = .free then some (g, rel) else none)
        ; if s = .free then
            writeGuard γ g v ∗
            □ (∀ v₁ : T, writeGuard γ g v₁ -∗
                 ⟪ ∀ s' v₀, isRwLock γ lk s' v₀ ⟫ Hd m (rel g) @ (∅ : CoPset)
                   ⟪ isRwLock γ lk .free v₁ ∗ ⌜s' = .write⌝ | RET () ⟫)
          else emp ⟫

  /-- Releasing a read guard retries its decrement, so its closure is stated at
  `.part` even though acquiring did not have to block. -/
  try_read_spec {T : Type} (γ : GName) (lk : RwLock T) :
    ⊢ ⟪ ∀ s v, isRwLock γ lk s v ⟫ Hd m (try_read lk) @ (∅ : CoPset)
        ⟪ isRwLock γ lk (match s with
                         | .free => .read 0
                         | .read n => .read (n + 1)
                         | .write => .write) v
        | g rel, RET (if s = .write then none else some (g, rel))
        ; if s = .write then emp else
            readGuardFrac γ g 1 v ∗
            □ (readGuardFrac γ g 1 v -∗
                 ⟪ ∀ s', isRwLock γ lk s' v ⟫ Hd .part (rel g) @ (∅ : CoPset)
                   ⟪ (isRwLock γ lk .free v ∗ ⌜s' = .read 0⌝) ∨
                     (∃ n : Nat, isRwLock γ lk (.read n) v ∗ ⌜s' = .read (n + 1)⌝)
                   | RET () ⟫) ⟫

  /-- Blocking acquires spin, so they are only partially correct: a thread that
  never wins the race owes nothing.

  The release closure opens its update at an *arbitrary* state and returns
  `⌜s' = .write⌝`, rather than demanding `.write` up front.  This matters because
  the guard is surrendered to the closure before the update is opened, so a caller
  holding only the update has nothing left to prove `.write` with; requiring it
  would force every caller to park a witness in its own invariant and reason about
  fractions of it.  `read_spec` below already returns the state it found. -/
  write_spec {T : Type} (γ : GName) (lk : RwLock T) :
    ⊢ ⟪ ∀ s v, isRwLock γ lk s v ⟫ Hd .part (write lk) @ (∅ : CoPset)
        ⟪ isRwLock γ lk .write v ∗ ⌜s = .free⌝
        | g rel, RET (g, rel)
        ; writeGuard γ g v ∗
          □ (∀ v₁ : T, writeGuard γ g v₁ -∗
               ⟪ ∀ s' v₀, isRwLock γ lk s' v₀ ⟫ Hd .part (rel g) @ (∅ : CoPset)
                   ⟪ isRwLock γ lk .free v₁ ∗ ⌜s' = .write⌝ | RET () ⟫) ⟫

  read_spec {T : Type} (γ : GName) (lk : RwLock T) :
    ⊢ ⟪ ∀ s v, isRwLock γ lk s v ⟫ Hd .part (read lk) @ (∅ : CoPset)
        ⟪ (isRwLock γ lk (.read 0) v ∗ ⌜s = .free⌝) ∨
          (∃ k : Nat, isRwLock γ lk (.read (k + 1)) v ∗ ⌜s = .read k⌝)
        | g rel, RET (g, rel)
        ; readGuardFrac γ g 1 v ∗
          □ (readGuardFrac γ g 1 v -∗
               ⟪ ∀ s', isRwLock γ lk s' v ⟫ Hd .part (rel g) @ (∅ : CoPset)
                   ⟪ (isRwLock γ lk .free v ∗ ⌜s' = .read 0⌝) ∨
                     (∃ n : Nat, isRwLock γ lk (.read n) v ∗ ⌜s' = .read (n + 1)⌝)
                   | RET () ⟫) ⟫

  write_deref_spec {T : Type} (γ : GName) (g : WriteGuard T) (v : T) (M : CoPset) :
    ⦃ writeGuard γ g v ⦄ (write_deref g) @ Hd ; m ; M
    ⦃ r, ⌜r = v⌝ ∗ writeGuard γ g v ⦄

  read_deref_spec {T : Type} (γ : GName) (g : ReadGuard T) (q : Qp) (v : T) (M : CoPset) :
    ⦃ readGuardFrac γ g q v ⦄ (read_deref g) @ Hd ; m ; M
    ⦃ r, ⌜r = v⌝ ∗ readGuardFrac γ g q v ⦄

  /-- The inner `set` obligation stays a `wpi_mask`: it is a nested triple, and
  `⦃ ⦄` does not nest inside an `iprop`. -/
  write_deref_mut_spec {T : Type} (γ : GName) (g : WriteGuard T) (v : T) (M : CoPset) :
    ⦃ writeGuard γ g v ⦄ (write_deref_mut g) @ Hd ; m ; M
    ⦃ r, ∃ set, ⌜r = (v, set, fun g' => g')⌝ ∗
        writeGuard γ g v ∗
        □ (∀ v₀ : T, ∀ v' : T, writeGuard γ g v₀ -∗
             wpi_mask GF Hd m (set v')
               (fun g' => iprop(⌜g' = g⌝ ∗ writeGuard γ g v')) ⊤) ⦄

attribute [instance] RwLockAPI.isRwLock_timeless RwLockAPI.writeGuard_timeless
attribute [instance] RwLockAPI.readGuardFrac_timeless

end Interface

end AeneasIris
