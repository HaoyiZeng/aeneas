import AeneasIris.HeapAPI
import Iris.Algebra.Auth
import Iris.Algebra.LocalUpdates

namespace AeneasIris.RwLock

open Iris BI Aeneas.Data.Coinductive
open AeneasIris AeneasIris.Heap AeneasIris.HeapAPI
open Aeneas.Std (StateE StepE Loc Val RustHeap)
open scoped Aeneas.Std
open AeneasIris.Step (lat LaterModality stepH)
open Iris.CMRA Iris.OFE
open scoped Iris

def RwPos : Type := { q : Rat // 0 < q }

namespace RwPos

def val (x : RwPos) : Rat := x.1
theorem pos (x : RwPos) : 0 < x.val := x.2
theorem ext {x y : RwPos} (h : x.val = y.val) : x = y := Subtype.ext h
@[simp] theorem ext_iff {x y : RwPos} : x = y ↔ x.val = y.val := Subtype.ext_iff

instance : Add RwPos :=
  ⟨fun x y => ⟨x.val + y.val, by have := x.pos; have := y.pos; grind⟩⟩
instance : One RwPos := ⟨⟨1, by grind⟩⟩

@[simp] theorem val_add (x y : RwPos) : (x + y).val = x.val + y.val := rfl
@[simp] theorem val_one : (1 : RwPos).val = 1 := rfl

def ofQp (q : Qp) : RwPos := ⟨q.val, q.2⟩
@[simp] theorem ofQp_val (q : Qp) : (ofQp q).val = q.val := rfl
@[simp] theorem ofQp_one : ofQp 1 = (1 : RwPos) := ext rfl
@[simp] theorem ofQp_add (q₁ q₂ : Qp) : ofQp (q₁ + q₂) = ofQp q₁ + ofQp q₂ := ext rfl
theorem ofQp_inj {a b : Qp} (h : ofQp a = ofQp b) : a = b := Subtype.ext (congrArg val h)

def ofSucc (n : Nat) : RwPos := ⟨(n : Rat) + 1, by have : (0:Rat) ≤ (n : Rat) := Rat.natCast_nonneg; grind⟩
@[simp] theorem ofSucc_val (n : Nat) : (ofSucc n).val = (n : Rat) + 1 := rfl
@[simp] theorem ofSucc_zero : ofSucc 0 = (1 : RwPos) := ext (by show ((0:Nat) : Rat) + 1 = 1; grind)

instance : COFE RwPos := COFE.ofDiscrete _ Eq_Equivalence
instance : OFE.Discrete RwPos := ⟨congrArg id⟩
instance : OFE.Leibniz RwPos := ⟨congrArg id⟩

instance : CMRA RwPos where
  pcore _ := none
  op x y := x + y
  ValidN _ _ := True
  Valid _ := True
  op_ne.ne n x1 x2 H := by rw [H]
  pcore_ne _ H := by rcases H
  validN_ne _ := id
  valid_iff_validN := .symm (forall_const _)
  validN_succ := id
  validN_op_left _ := trivial
  assoc := OFE.leibniz.mpr <| ext (Rat.add_assoc ..).symm
  comm := OFE.leibniz.mpr <| ext (Rat.add_comm ..)
  pcore_op_left H := by rcases H
  pcore_idem H := by rcases H
  pcore_op_mono H := by rcases H
  extend {_ x y z} := by rintro _ rfl; exists y; exists z

instance : CMRA.Discrete RwPos where
  discrete_0 := id
  discrete_valid _ := trivial

@[simp] theorem op_eq (x y : RwPos) : x • y = x + y := rfl
@[simp] theorem valid (x : RwPos) : ✓ x := trivial

theorem not_incl_self (x : RwPos) : ¬ (x ≼ x) := by
  rintro ⟨c, hc⟩
  have h : x.val = x.val + c.val := congrArg Subtype.val hc
  have := c.pos
  grind

end RwPos

abbrev RwRes := Option (RwPos × RwPos)
abbrev RwSpinF : COFE.OFunctorPre := Auth.AuthURF (constOF RwRes)

class RwSpinG (GF : BundledGFunctors) where
  [rwSpinG : ElemG GF RwSpinF]

attribute [reducible, instance] RwSpinG.rwSpinG

inductive LockState
  | free
  | read (n : Nat)
  | write
deriving DecidableEq, Repr

def LockState.word : LockState → Int
  | .free => 0
  | .read n => (n : Int) + 1
  | .write => -1

theorem LockState.word_injective : Function.Injective LockState.word := by
  intro a b h
  cases a <;> cases b <;> simp_all [LockState.word] <;> omega

/-- Model of `my_std::RwLock<T>`.

The Rust type is opaque, so its representation is ours to choose: the two cells
the implementation actually runs on — a state word and the payload. `T` is
phantom here for the same reason it is in Rust, where the payload sits behind
the pointer rather than inside the struct. -/
structure Handle (T : Type) where
  state : Loc
  data : Loc
deriving DecidableEq, Repr

/-- Model of `my_std::RwLockReadGuard<'_, T>`.

A guard is the lock it was taken from -- but it is a *distinct type*, not an
abbreviation for `Handle`, exactly as in Rust. The two guards stand for
different permissions, so nothing should typecheck that releases one through
the other's path, or derefs a read guard mutably. -/
structure ReadGuard (T : Type) where
  lock : Handle T
deriving DecidableEq, Repr

/-- Model of `my_std::RwLockWriteGuard<'_, T>`. Distinct from `ReadGuard`. -/
structure WriteGuard (T : Type) where
  lock : Handle T
deriving DecidableEq, Repr

section Code

variable {E : Effect.{1}} [StateE RustHeap.{0} -< E] [StepE.{1} -< E]
variable {T : Type} [Nonempty T]

noncomputable def new (v : T) : ITree E (Handle T) := do
  let d ← alloc v
  let s ← alloc (0 : Int)
  return ⟨s, d⟩

noncomputable def try_read (lk : Handle T) : ITree E (Option (ReadGuard T)) := do
  let n : Int ← load lk.state
  if n < 0 then
    return none
  else
    let ok ← cas lk.state n (n + 1)
    if ok then return some ⟨lk⟩ else return none

noncomputable def try_write (lk : Handle T) : ITree E (Option (WriteGuard T)) := do
  let ok ← cas lk.state (0 : Int) (-1)
  if ok then return some ⟨lk⟩ else return none

noncomputable def read_acquire (lk : Handle T) : ITree E (ReadGuard T) :=
  ITree.iter (fun _ => do
    match ← try_read (E := E) lk with
    | some g => return .inr g
    | none => return .inl ()) ()

noncomputable def write_acquire (lk : Handle T) : ITree E (WriteGuard T) :=
  ITree.iter (fun _ => do
    match ← try_write (E := E) lk with
    | some g => return .inr g
    | none => return .inl ()) ()

noncomputable def read_release (g : ReadGuard T) : ITree E Unit :=
  ITree.iter (fun _ => do
    let n : Int ← load g.lock.state
    let ok ← cas g.lock.state n (n - 1)
    if ok then return .inr () else return .inl ()) ()

def write_release (g : WriteGuard T) : ITree E Unit := do
  store g.lock.state (0 : Int)

/-- `my_std::RwLock::read`.

Aeneas hands back a borrow as the value paired with its backward function, and
for a guard that backward function *is* the release -- which is literally what
the generated code does:

    let p ← acquire_exclusive_lock self
    let (_lock, back) := p
    ...
    back _lock

So the pair is `(guard, release)`. No `GuardKind` tag is needed for two
independent reasons: the guard types are distinct, and the only release a
caller is ever handed is the one this call built.

Written with an explicit `ITree.bind` rather than `do`: the payload crosses a
universe here (`ReadGuard T` is `Type 0`, the release function is `Type 1`) and
the `Monad` instance pins a single one. `ITree.bind` is already cross-universe. -/
noncomputable def read (lk : Handle T) :
    ITree E (ReadGuard T × (ReadGuard T → ITree E Unit)) :=
  ITree.bind (read_acquire (E := E) lk) (fun g => .ret (g, read_release))

noncomputable def write (lk : Handle T) :
    ITree E (WriteGuard T × (WriteGuard T → ITree E Unit)) :=
  ITree.bind (write_acquire (E := E) lk) (fun g => .ret (g, write_release))

/-- `Deref for RwLockReadGuard`: `&self`, so there is no backward function. -/
noncomputable def read_deref (g : ReadGuard T) : ITree E T :=
  load g.lock.data

/-- `Deref for RwLockWriteGuard`: also `&self`, hence also no backward. -/
noncomputable def write_deref (g : WriteGuard T) : ITree E T :=
  load g.lock.data

/-- `DerefMut for RwLockWriteGuard`.

`&mut T` out of `&mut self` gives Aeneas a triple: the value, the backward
function of the borrow that was returned (write the new value into the cell),
and the backward function of `self` (the guard itself is unchanged). -/
noncomputable def write_deref_mut (g : WriteGuard T) :
    ITree E (T × (T → ITree E (WriteGuard T)) × (WriteGuard T → ITree E (WriteGuard T))) :=
  ITree.bind (load (E := E) g.lock.data) (fun v =>
    .ret (v, (fun w => ITree.bind (store g.lock.data w) (fun _ => .ret g)),
             (fun g' => .ret g')))

/-- `Drop for RwLockReadGuard`.

The second component is a computation, not a function: a shared borrow takes no
input back, so its backward degenerates to "the release, still to be run". -/
noncomputable def read_drop (g : ReadGuard T) : ITree E (ReadGuard T × ITree E Unit) :=
  .ret (g, read_release g)

/-- `Drop for RwLockWriteGuard`. -/
noncomputable def write_drop (g : WriteGuard T) :
    ITree E (WriteGuard T × (WriteGuard T → ITree E (WriteGuard T))) :=
  ITree.bind (write_release g) (fun _ => .ret (g, fun g' => .ret g'))

def drop (lk : Handle T) : ITree E Unit := do
  let _ ← HeapAPI.free lk.data
  HeapAPI.free lk.state

end Code

section Assertions

variable {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF] [G : HeapGS.{0} GF]
variable {T : Type}

def isRwLock (lk : Handle T) (s : LockState) (v : T) : IProp GF :=
  iprop(lk.state ↦ s.word ∗ lk.data ↦ v)

def writeGuard (lk : Handle T) (v : T) : IProp GF :=
  iprop(lk.data ↦ v)

def readGuardFrac (lk : Handle T) (q : Qp) (v : T) : IProp GF :=
  iprop(lk.data ↦{DFrac.own q} v)

instance (lk : Handle T) (s : LockState) (v : T) :
    Timeless (PROP := IProp GF) (isRwLock lk s v) := by
  unfold isRwLock; infer_instance

instance (lk : Handle T) (v : T) :
    Timeless (PROP := IProp GF) (writeGuard lk v) := by
  unfold writeGuard; infer_instance

instance (lk : Handle T) (q : Qp) (v : T) :
    Timeless (PROP := IProp GF) (readGuardFrac lk q v) := by
  unfold readGuardFrac; infer_instance

theorem readGuardFrac_split (lk : Handle T) (q₁ q₂ : Qp) (v : T) :
    readGuardFrac (GF := GF) lk (q₁ + q₂) v
      ⊣⊢ iprop(readGuardFrac lk q₁ v ∗ readGuardFrac lk q₂ v) := by
  unfold readGuardFrac
  exact (Fractional.fractional (Φ := fun q => pointsTo lk.data (DFrac.own q) v) q₁ q₂)

theorem isRwLock_exclusive (lk : Handle T) (s₁ s₂ : LockState) (v₁ v₂ : T) :
    iprop(isRwLock lk s₁ v₁ ∗ isRwLock lk s₂ v₂) ⊢@{IProp GF} iprop(False) := by
  sorry

theorem isRwLock_agree (lk : Handle T) (s₁ s₂ : LockState) (v₁ v₂ : T) :
    iprop(isRwLock lk s₁ v₁ ∗ isRwLock lk s₂ v₂) ⊢@{IProp GF} iprop(⌜s₁ = s₂ ∧ v₁ = v₂⌝) := by
  sorry

end Assertions

end AeneasIris.RwLock
