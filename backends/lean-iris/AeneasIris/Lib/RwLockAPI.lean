import AeneasIris.Tactics.Core
import AeneasIris.AtomicWpi
import Iris.BI.Lib.Atomic

/-! # The `RwLock` interface -/

namespace AeneasIris

open Iris BI Aeneas.Data.Coinductive
open AeneasIris.AtomicWpi

/-- The abstract state of a lock: free, `n + 1` readers, or one writer. -/
inductive LockState
  | free
  | read (n : Nat)
  | write
deriving DecidableEq, Repr

section Interface

variable {hlc : Iris.HasLC}

/-- A reader/writer lock over `T`, as a menu of operations, three abstract
predicates, and the laws relating them.

Generic in the effect row `E`, the handler `Hd` and the `Mode`, so a client
programs against the interface at whatever language it is itself written in. The
carrier types are `outParam`s: an implementation chooses them, and a client
names them without spelling out which implementation it meant. -/
class RwLockAPI (GF : BundledGFunctors) [Iris.InvGS_gen hlc GF]
    {E : Effect.{1}} (Hd : Handler E GF) (m : Mode) (T : Type)
    (Handle ReadGuard WriteGuard : outParam Type) where
  new : T → ITree E Handle
  drop : Handle → ITree E Unit
  try_read : Handle → ITree E (Option (ReadGuard × (ReadGuard → ITree E Unit)))
  try_write : Handle → ITree E (Option (WriteGuard × (WriteGuard → ITree E Unit)))
  read : Handle → ITree E (ReadGuard × (ReadGuard → ITree E Unit))
  write : Handle → ITree E (WriteGuard × (WriteGuard → ITree E Unit))
  read_deref : ReadGuard → ITree E T
  write_deref : WriteGuard → ITree E T
  write_deref_mut : WriteGuard →
    ITree E (T × (T → ITree E WriteGuard) × (WriteGuard → ITree E WriteGuard))

  /-- The lock itself, at abstract state `s` holding `v`. -/
  isRwLock : GName → Handle → LockState → T → IProp GF
  /-- Exclusive access to the contents, held *through* `g`.

  Keyed on the guard, not on the lock, so that a guard is the opaque RAII token
  Rust has it be: a client never names one, it receives one from an acquire and
  spends it on a deref or a release.  Which lock is meant is recovered from the
  ghost name, so no acquire has to relate its result back to the lock. -/
  writeGuard : GName → WriteGuard → T → IProp GF
  /-- Shared access at client-visible strength `q`, likewise held through `g`. -/
  readGuardFrac : GName → ReadGuard → Qp → T → IProp GF

  isRwLock_timeless γ lk s v : Timeless (isRwLock γ lk s v)
  writeGuard_timeless γ g v : Timeless (writeGuard γ g v)
  readGuardFrac_timeless γ g q v : Timeless (readGuardFrac γ g q v)

  isRwLock_exclusive γ lk s₁ s₂ v₁ v₂ :
    iprop(isRwLock γ lk s₁ v₁ ∗ isRwLock γ lk s₂ v₂) ⊢@{IProp GF} iprop(False)
  readGuardFrac_split γ g q₁ q₂ v :
    iprop(readGuardFrac γ g (q₁ + q₂) v)
      ⊣⊢ iprop(readGuardFrac γ g q₁ v ∗ readGuardFrac γ g q₂ v)
  readGuardFrac_state γ lk s g q v v' :
    iprop(isRwLock γ lk s v ∗ readGuardFrac γ g q v') ⊢@{IProp GF} iprop(⌜∃ n, s = .read n⌝)
  readGuardFrac_agree γ lk s g q v v' :
    iprop(isRwLock γ lk s v ∗ readGuardFrac γ g q v') ⊢@{IProp GF} iprop(⌜v = v'⌝)
  writeGuard_state γ lk s g v v' :
    iprop(isRwLock γ lk s v ∗ writeGuard γ g v') ⊢@{IProp GF} iprop(⌜s = .write⌝)

  new_spec (v : T) (M : CoPset) :
    ⦃ emp ⦄ (new v) @ Hd ; m ; M ⦃ lk, ∃ γ, isRwLock γ lk .free v ⦄

  drop_spec (γ : GName) (lk : Handle) (v : T) (M : CoPset) :
    ⦃ isRwLock γ lk .free v ⦄ (drop lk) @ Hd ; m ; M ⦃ r, ⌜r = ()⌝ ⦄

  try_write_spec (γ : GName) (lk : Handle) :
    ⊢ ⟪ ∀ s v, isRwLock γ lk s v ⟫ Hd m (try_write lk) @ (∅ : CoPset)
        ⟪ isRwLock γ lk (if s = .free then .write else s) v
        | g rel, RET (if s = .free then some (g, rel) else none)
        ; if s = .free then
            writeGuard γ g v ∗
            □ (∀ v₁ : T, writeGuard γ g v₁ -∗
                 ⟪ ∀ v₀, isRwLock γ lk .write v₀ ⟫ Hd m (rel g) @ (∅ : CoPset)
                   ⟪ isRwLock γ lk .free v₁ | RET () ⟫)
          else emp ⟫

  /-- Releasing a read guard retries its decrement, so its closure is stated at
  `.part` even though acquiring did not have to block. -/
  try_read_spec (γ : GName) (lk : Handle) :
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
  never wins the race owes nothing. -/
  write_spec (γ : GName) (lk : Handle) :
    ⊢ ⟪ ∀ s v, isRwLock γ lk s v ⟫ Hd .part (write lk) @ (∅ : CoPset)
        ⟪ isRwLock γ lk .write v ∗ ⌜s = .free⌝
        | g rel, RET (g, rel)
        ; writeGuard γ g v ∗
          □ (∀ v₁ : T, writeGuard γ g v₁ -∗
               ⟪ ∀ v₀, isRwLock γ lk .write v₀ ⟫ Hd .part (rel g) @ (∅ : CoPset)
                   ⟪ isRwLock γ lk .free v₁ | RET () ⟫) ⟫

  read_spec (γ : GName) (lk : Handle) :
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

  write_deref_spec (γ : GName) (g : WriteGuard) (v : T) (M : CoPset) :
    ⦃ writeGuard γ g v ⦄ (write_deref g) @ Hd ; m ; M
    ⦃ r, ⌜r = v⌝ ∗ writeGuard γ g v ⦄

  read_deref_spec (γ : GName) (g : ReadGuard) (q : Qp) (v : T) (M : CoPset) :
    ⦃ readGuardFrac γ g q v ⦄ (read_deref g) @ Hd ; m ; M
    ⦃ r, ⌜r = v⌝ ∗ readGuardFrac γ g q v ⦄

  /-- The inner `set` obligation stays a `wpi_mask`: it is a nested triple, and
  `⦃ ⦄` does not nest inside an `iprop`. -/
  write_deref_mut_spec (γ : GName) (g : WriteGuard) (v : T) (M : CoPset) :
    ⦃ writeGuard γ g v ⦄ (write_deref_mut g) @ Hd ; m ; M
    ⦃ r, ∃ set back, ⌜r = (v, set, back)⌝ ∗
        writeGuard γ g v ∗
        □ (∀ v₀ : T, ∀ v' : T, writeGuard γ g v₀ -∗
             wpi_mask GF Hd m (set v')
               (fun g' => iprop(⌜g' = g⌝ ∗ writeGuard γ g v')) ⊤) ⦄

attribute [instance] RwLockAPI.isRwLock_timeless RwLockAPI.writeGuard_timeless
attribute [instance] RwLockAPI.readGuardFrac_timeless

end Interface

end AeneasIris
