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

def LockState.word : LockState → Int
  | .free => 0
  | .read n => (n : Int) + 1
  | .write => -1

theorem LockState.word_injective :
    Function.Injective LockState.word := by
  intro a b h
  cases a <;> cases b <;> simp_all [AeneasIris.LockState.word] <;> grind

section Interface

variable {hlc : Iris.HasLC}

/-! ## Release obligations

`write` and `try_write` owe their release closure the same thing, and so do
`read` and `try_read`; only the argument the closure is applied to differs
(`g` versus `some g`).  Naming the obligation is not just tidiness: stating it
four times over left the class field and the implementing theorem as two
structurally equal but distinct terms, and unifying them at the instance
declaration timed out `isDefEq`.  With one definition on both sides the check
is a matter of matching a head symbol. -/

section Obligations
variable {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF] {E : Effect.{1}}
variable (Hd : Handler E GF) (m : Mode)

/-- Hand the guard back, and the lock is `.free` holding whatever the guard
carried; the state found is reported rather than demanded, so a caller holding
only the update has nothing left to prove. -/
@[reducible] def WriteReleases {L W T : Type}
    (isRwLock : GName → L → LockState → T → IProp GF)
    (writeGuard : GName → W → T → IProp GF)
    (γ : GName) (lk : L) (g : W) (rel : ITree E Unit) : IProp GF :=
  iprop(□ (∀ v₁ : T, writeGuard γ g v₁ -∗
    ⟪ ∀ s' v₀, isRwLock γ lk s' v₀ ⟫ Hd m rel @ (∅ : CoPset)
      ⟪ isRwLock γ lk .free v₁ ∗ ⌜s' = .write⌝ | RET () ⟫))

/-- Hand a full read share back, and the reader count drops by one -- to
`.free` if it was the last. -/
@[reducible] def ReadReleases {L R T : Type}
    (isRwLock : GName → L → LockState → T → IProp GF)
    (readGuardFrac : GName → R → Qp → T → IProp GF)
    (γ : GName) (lk : L) (g : R) (v : T) (rel : ITree E Unit) : IProp GF :=
  iprop(□ (readGuardFrac γ g 1 v -∗
    ⟪ ∀ s' v₀, isRwLock γ lk s' v₀ ⟫ Hd m rel @ (∅ : CoPset)
      ⟪ (isRwLock γ lk .free v₀ ∗ ⌜s' = .read 0⌝) ∨
        (∃ n : Nat, isRwLock γ lk (.read n) v₀ ∗ ⌜s' = .read (n + 1)⌝)
      | RET () ⟫))

/-! Unfolding lemmas.  The definitions exist to keep the class field and the
implementing theorem a single term; clients that were written against the
spelled-out form should not have to care, so `simp` puts it back. -/

@[simp] theorem WriteReleases_def {L W T : Type}
    (isRwLock : GName → L → LockState → T → IProp GF)
    (writeGuard : GName → W → T → IProp GF)
    (γ : GName) (lk : L) (g : W) (rel : ITree E Unit) :
    WriteReleases Hd m isRwLock writeGuard γ lk g rel
      = iprop(□ (∀ v₁ : T, writeGuard γ g v₁ -∗
          ⟪ ∀ s' v₀, isRwLock γ lk s' v₀ ⟫ Hd m rel @ (∅ : CoPset)
            ⟪ isRwLock γ lk .free v₁ ∗ ⌜s' = .write⌝ | RET () ⟫)) := rfl

@[simp] theorem ReadReleases_def {L R T : Type}
    (isRwLock : GName → L → LockState → T → IProp GF)
    (readGuardFrac : GName → R → Qp → T → IProp GF)
    (γ : GName) (lk : L) (g : R) (v : T) (rel : ITree E Unit) :
    ReadReleases Hd m isRwLock readGuardFrac γ lk g v rel
      = iprop(□ (readGuardFrac γ g 1 v -∗
          ⟪ ∀ s' v₀, isRwLock γ lk s' v₀ ⟫ Hd m rel @ (∅ : CoPset)
            ⟪ (isRwLock γ lk .free v₀ ∗ ⌜s' = .read 0⌝) ∨
              (∃ n : Nat, isRwLock γ lk (.read n) v₀ ∗ ⌜s' = .read (n + 1)⌝)
            | RET () ⟫)) := rfl

/-- Both obligations are `□`, so callers may `icases` them out as persistent
without unfolding first. -/
instance WriteReleases_persistent {L W T : Type}
    (isRwLock : GName → L → LockState → T → IProp GF)
    (writeGuard : GName → W → T → IProp GF)
    (γ : GName) (lk : L) (g : W) (rel : ITree E Unit) :
    Persistent (WriteReleases Hd m isRwLock writeGuard γ lk g rel) := by
  unfold WriteReleases; infer_instance

instance ReadReleases_persistent {L R T : Type}
    (isRwLock : GName → L → LockState → T → IProp GF)
    (readGuardFrac : GName → R → Qp → T → IProp GF)
    (γ : GName) (lk : L) (g : R) (v : T) (rel : ITree E Unit) :
    Persistent (ReadReleases Hd m isRwLock readGuardFrac γ lk g v rel) := by
  unfold ReadReleases; infer_instance

/-- What a `try_write` hands back: nothing but the reason it failed, or the
guard together with its release obligation.  Named for the same reason as
`WriteReleases`. -/
@[reducible] def TryWriteResult {L W T : Type}
    (isRwLock : GName → L → LockState → T → IProp GF)
    (writeGuard : GName → W → T → IProp GF)
    (γ : GName) (lk : L) (s : LockState) (v : T)
    (og : Option W) (rel : Option W → ITree E Unit) : IProp GF :=
  match og with
  | none => iprop(⌜s ≠ .free⌝)
  | some g => iprop(⌜s = .free⌝ ∗ writeGuard γ g v ∗
      WriteReleases Hd m isRwLock writeGuard γ lk g (rel (some g)))

/-- The `try_read` counterpart. -/
@[reducible] def TryReadResult {L R T : Type}
    (isRwLock : GName → L → LockState → T → IProp GF)
    (readGuardFrac : GName → R → Qp → T → IProp GF)
    (γ : GName) (lk : L) (s : LockState) (v : T)
    (og : Option R) (rel : Option R → ITree E Unit) : IProp GF :=
  match og with
  | none => iprop(⌜s = .write⌝)
  | some g => iprop(⌜s ≠ .write⌝ ∗ readGuardFrac γ g 1 v ∗
      ReadReleases Hd m isRwLock readGuardFrac γ lk g v (rel (some g)))

end Obligations

/-- A reader/writer lock over `T`, as a menu of operations, three abstract
predicates, and the laws relating them.

Generic in the effect row `E`, the handler `Hd` and the `Mode`, so a client
programs against the interface at whatever language it is itself written in.

The carriers are type *constructors*, as `RwLock<T>` is in Rust: one
implementation serves every `T`, rather than one instance per `T`.

They are fields rather than parameters because they are not independent choices:
an implementation supplies all three together, and no client should be able to
pair one implementation's lock with another's guard.  Instance search therefore
runs on `GF`, `Hd` and `m` alone, which is also what lets `new` -- whose result
type is the lock -- elaborate without an annotation. -/
class RwLockAPI (GF : BundledGFunctors) [Iris.InvGS_gen hlc GF]
    {E : Effect.{1}} (Hd : Handler E GF) (m : Mode) where
  RwLock : Type → Type
  ReadGuard : Type → Type
  WriteGuard : Type → Type

  new {T : Type} : T → ITree E (RwLock T)
  drop {T : Type} : RwLock T → ITree E Unit
  /-- The `Option` is on the guard alone, and the closure is beside it rather
  than inside it: `try_read` borrows the lock whether or not it acquires, so
  there is always exactly one borrow to end, and its final value is what may or
  may not hold a guard. -/
  try_read {T : Type} :
    RwLock T → ITree E (Option (ReadGuard T) × (Option (ReadGuard T) → ITree E Unit))
  try_write {T : Type} :
    RwLock T → ITree E (Option (WriteGuard T) × (Option (WriteGuard T) → ITree E Unit))
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
        | og rel, RET (og, rel)
        ; ⌜rel none = ITree.ret ()⌝ ∗
          TryWriteResult Hd m isRwLock writeGuard γ lk s v og rel ⟫

  /-- Releasing a read guard retries its decrement, so its closure is stated at
  `.part` even though acquiring did not have to block. -/
  try_read_spec {T : Type} (γ : GName) (lk : RwLock T) :
    ⊢ ⟪ ∀ s v, isRwLock γ lk s v ⟫ Hd .part (try_read lk) @ (∅ : CoPset)
        ⟪ isRwLock γ lk (match s with
                         | .free => .read 0
                         | .read n => .read (n + 1)
                         | .write => .write) v
        | og rel, RET (og, rel)
        ; ⌜rel none = ITree.ret ()⌝ ∗
          TryReadResult Hd .part isRwLock readGuardFrac γ lk s v og rel ⟫

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
          WriteReleases Hd .part isRwLock writeGuard γ lk g (rel g) ⟫

  read_spec {T : Type} (γ : GName) (lk : RwLock T) :
    ⊢ ⟪ ∀ s v, isRwLock γ lk s v ⟫ Hd .part (read lk) @ (∅ : CoPset)
        ⟪ (isRwLock γ lk (.read 0) v ∗ ⌜s = .free⌝) ∨
          (∃ k : Nat, isRwLock γ lk (.read (k + 1)) v ∗ ⌜s = .read k⌝)
        | g rel, RET (g, rel)
        ; readGuardFrac γ g 1 v ∗
          ReadReleases Hd .part isRwLock readGuardFrac γ lk g v (rel g) ⟫

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
