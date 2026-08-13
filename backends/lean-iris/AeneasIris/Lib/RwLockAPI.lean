import AeneasIris.Tactics.Core
import AeneasIris.AtomicWpi
import Iris.BI.Lib.Atomic

/-! # The `RwLock` interface -/

namespace AeneasIris.RwLockAPI

open Iris BI Aeneas.Data.Coinductive
open AeneasIris AeneasIris.AtomicWpi

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

  /-- The guard's lock, so that a spec about a guard can name the lock it guards. -/
  readLock : ReadGuard → Handle
  writeLock : WriteGuard → Handle
  /-- The guard a successful acquire on a lock hands back.

  Exposed rather than existentially quantified in the acquire specs, because the
  guard *is* determined by the lock in any implementation, and quantifying it
  would force every such spec to be stated with an extra binder that the
  implementation then has to instantiate by hand. -/
  mkReadGuard : Handle → ReadGuard
  mkWriteGuard : Handle → WriteGuard
  readLock_mk lk : readLock (mkReadGuard lk) = lk
  writeLock_mk lk : writeLock (mkWriteGuard lk) = lk

  /-- The lock itself, at abstract state `s` holding `v`. -/
  isRwLock : GName → Handle → LockState → T → IProp GF
  /-- Exclusive access to the contents. -/
  writeGuard : GName → Handle → T → IProp GF
  /-- Shared access at client-visible strength `q`. -/
  readGuardFrac : GName → Handle → Qp → T → IProp GF

  isRwLock_timeless γ lk s v : Timeless (isRwLock γ lk s v)
  writeGuard_timeless γ lk v : Timeless (writeGuard γ lk v)
  readGuardFrac_timeless γ lk q v : Timeless (readGuardFrac γ lk q v)

  isRwLock_exclusive γ lk s₁ s₂ v₁ v₂ :
    iprop(isRwLock γ lk s₁ v₁ ∗ isRwLock γ lk s₂ v₂) ⊢@{IProp GF} iprop(False)
  readGuardFrac_split γ lk q₁ q₂ v :
    iprop(readGuardFrac γ lk (q₁ + q₂) v)
      ⊣⊢ iprop(readGuardFrac γ lk q₁ v ∗ readGuardFrac γ lk q₂ v)
  readGuardFrac_state γ lk s q v v' :
    iprop(isRwLock γ lk s v ∗ readGuardFrac γ lk q v') ⊢@{IProp GF} iprop(⌜∃ n, s = .read n⌝)
  readGuardFrac_agree γ lk s q v v' :
    iprop(isRwLock γ lk s v ∗ readGuardFrac γ lk q v') ⊢@{IProp GF} iprop(⌜v = v'⌝)
  writeGuard_state γ lk s v v' :
    iprop(isRwLock γ lk s v ∗ writeGuard γ lk v') ⊢@{IProp GF} iprop(⌜s = .write⌝)

  new_spec (v : T) (M : CoPset) :
    ⦃ emp ⦄ (new v) @ Hd ; m ; M ⦃ lk, ∃ γ, isRwLock γ lk .free v ⦄

  drop_spec (γ : GName) (lk : Handle) (v : T) (M : CoPset) :
    ⦃ isRwLock γ lk .free v ⦄ (drop lk) @ Hd ; m ; M ⦃ r, ⌜r = ()⌝ ⦄

  try_write_spec (γ : GName) (lk : Handle) :
    ⊢ ⟪ ∀ s v, isRwLock γ lk s v ⟫ Hd m (try_write lk) @ (∅ : CoPset)
        ⟪ isRwLock γ lk (if s = .free then .write else s) v
        | rel, RET (if s = .free then some (mkWriteGuard lk, rel) else none)
        ; if s = .free then
            writeGuard γ lk v ∗
            □ (∀ v₁ : T, writeGuard γ lk v₁ -∗
                 ⟪ ∀ v₀, isRwLock γ lk .write v₀ ⟫
                     Hd m (rel (mkWriteGuard lk)) @ (∅ : CoPset)
                   ⟪ isRwLock γ lk .free v₁ | RET () ⟫)
          else emp ⟫

  write_spec (γ : GName) (lk : Handle) :
    ⊢ ⟪ ∀ s v, isRwLock γ lk s v ⟫ Hd m (write lk) @ (∅ : CoPset)
        ⟪ isRwLock γ lk .write v ∗ ⌜s = .free⌝
        | rel, RET (mkWriteGuard lk, rel)
        ; writeGuard γ lk v ∗
          □ (∀ v₁ : T, writeGuard γ lk v₁ -∗
               ⟪ ∀ v₀, isRwLock γ lk .write v₀ ⟫ Hd m (rel (mkWriteGuard lk)) @ (∅ : CoPset)
                   ⟪ isRwLock γ lk .free v₁ | RET () ⟫) ⟫

  try_read_spec (γ : GName) (lk : Handle) :
    ⊢ ⟪ ∀ s v, isRwLock γ lk s v ⟫ Hd m (try_read lk) @ (∅ : CoPset)
        ⟪ isRwLock γ lk (match s with
                         | .free => .read 0
                         | .read n => .read (n + 1)
                         | .write => .write) v
        | rel, RET (if s = .write then none else some (mkReadGuard lk, rel))
        ; if s = .write then emp else
            readGuardFrac γ lk 1 v ∗
            □ (readGuardFrac γ lk 1 v -∗
                 ⟪ ∀ s', isRwLock γ lk s' v ⟫
                     Hd m (rel (mkReadGuard lk)) @ (∅ : CoPset)
                   ⟪ (isRwLock γ lk .free v ∗ ⌜s' = .read 0⌝) ∨
                     (∃ n : Nat, isRwLock γ lk (.read n) v ∗ ⌜s' = .read (n + 1)⌝)
                   | RET () ⟫) ⟫

  read_spec (γ : GName) (lk : Handle) :
    ⊢ ⟪ ∀ s v, isRwLock γ lk s v ⟫ Hd m (read lk) @ (∅ : CoPset)
        ⟪ (isRwLock γ lk (.read 0) v ∗ ⌜s = .free⌝) ∨
          (∃ k : Nat, isRwLock γ lk (.read (k + 1)) v ∗ ⌜s = .read k⌝)
        | rel, RET (mkReadGuard lk, rel)
        ; readGuardFrac γ lk 1 v ∗
          □ (readGuardFrac γ lk 1 v -∗
               ⟪ ∀ s', isRwLock γ lk s' v ⟫ Hd m (rel (mkReadGuard lk)) @ (∅ : CoPset)
                   ⟪ (isRwLock γ lk .free v ∗ ⌜s' = .read 0⌝) ∨
                     (∃ n : Nat, isRwLock γ lk (.read n) v ∗ ⌜s' = .read (n + 1)⌝)
                   | RET () ⟫) ⟫

  write_deref_spec (γ : GName) (g : WriteGuard) (v : T) (M : CoPset) :
    ⦃ writeGuard γ (writeLock g) v ⦄ (write_deref g) @ Hd ; m ; M
    ⦃ r, ⌜r = v⌝ ∗ writeGuard γ (writeLock g) v ⦄

  read_deref_spec (γ : GName) (g : ReadGuard) (q : Qp) (v : T) (M : CoPset) :
    ⦃ readGuardFrac γ (readLock g) q v ⦄ (read_deref g) @ Hd ; m ; M
    ⦃ r, ⌜r = v⌝ ∗ readGuardFrac γ (readLock g) q v ⦄

  /-- The inner `set` obligation stays a `wpi_mask`: it is a nested triple, and
  `⦃ ⦄` does not nest inside an `iprop`. -/
  write_deref_mut_spec (γ : GName) (g : WriteGuard) (v : T) (M : CoPset) :
    ⦃ writeGuard γ (writeLock g) v ⦄ (write_deref_mut g) @ Hd ; m ; M
    ⦃ r, ∃ set back, ⌜r = (v, set, back)⌝ ∗
        writeGuard γ (writeLock g) v ∗
        □ (∀ v₀ : T, ∀ v' : T, writeGuard γ (writeLock g) v₀ -∗
             wpi_mask GF Hd m (set v')
               (fun g' => iprop(⌜g' = g⌝ ∗ writeGuard γ (writeLock g) v')) ⊤) ⦄

attribute [instance] RwLockAPI.isRwLock_timeless RwLockAPI.writeGuard_timeless
attribute [instance] RwLockAPI.readGuardFrac_timeless

end Interface

end AeneasIris.RwLockAPI
