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

structure Handle where
  state : Loc
  data : Loc
deriving DecidableEq, Repr

section Code

variable {E : Effect.{1}} [StateE RustHeap.{0} -< E] [StepE.{1} -< E]
variable {T : Type} [Nonempty T]

noncomputable def new (v : T) : ITree E Handle := do
  let d ← alloc v
  let s ← alloc (0 : Int)
  return ⟨s, d⟩

inductive GuardKind
  | read
  | write
deriving DecidableEq, Repr

noncomputable def try_read (lk : Handle) : ITree E (Option (Handle × GuardKind)) := do
  let n : Int ← load lk.state
  if n < 0 then
    return none
  else
    let ok ← cas lk.state n (n + 1)
    if ok then return some (lk, .read) else return none

noncomputable def try_write (lk : Handle) : ITree E (Option (Handle × GuardKind)) := do
  let ok ← cas lk.state (0 : Int) (-1)
  if ok then return some (lk, .write) else return none

noncomputable def read_acquire (lk : Handle) : ITree E Handle :=
  ITree.iter (fun _ => do
    match ← try_read (E := E) lk with
    | some (g, _) => return .inr g
    | none => return .inl ()) ()

noncomputable def write_acquire (lk : Handle) : ITree E Handle :=
  ITree.iter (fun _ => do
    match ← try_write (E := E) lk with
    | some (g, _) => return .inr g
    | none => return .inl ()) ()

noncomputable def read (lk : Handle) : ITree E (Handle × GuardKind) := do
  let g ← read_acquire (E := E) lk
  return (g, .read)

noncomputable def write (lk : Handle) : ITree E (Handle × GuardKind) := do
  let g ← write_acquire (E := E) lk
  return (g, .write)

noncomputable def read_release (lk : Handle) : ITree E Unit :=
  ITree.iter (fun _ => do
    let n : Int ← load lk.state
    let ok ← cas lk.state n (n - 1)
    if ok then return .inr () else return .inl ()) ()

def write_release (lk : Handle) : ITree E Unit := do
  store lk.state (0 : Int)

noncomputable def release (k : GuardKind) (lk : Handle) : ITree E Unit :=
  match k with
  | .read => read_release lk
  | .write => write_release lk

noncomputable def read_deref (lk : Handle) : ITree E T :=
  load lk.data

noncomputable def write_deref (lk : Handle) : ITree E T :=
  load lk.data

def write_set (lk : Handle) (v : T) : ITree E Unit := do
  store lk.data v

def drop (lk : Handle) : ITree E Unit := do
  let _ ← HeapAPI.free lk.data
  HeapAPI.free lk.state

end Code

section Assertions

variable {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF] [G : HeapGS.{0} GF]
variable {T : Type}

def isRwLock (lk : Handle) (s : LockState) (v : T) : IProp GF :=
  iprop(lk.state ↦ s.word ∗ lk.data ↦ v)

def writeGuard (lk : Handle) (v : T) : IProp GF :=
  iprop(lk.data ↦ v)

def readGuardFrac (lk : Handle) (q : Qp) (v : T) : IProp GF :=
  iprop(lk.data ↦{DFrac.own q} v)

instance (lk : Handle) (s : LockState) (v : T) :
    Timeless (PROP := IProp GF) (isRwLock lk s v) := by
  unfold isRwLock; infer_instance

instance (lk : Handle) (v : T) :
    Timeless (PROP := IProp GF) (writeGuard lk v) := by
  unfold writeGuard; infer_instance

instance (lk : Handle) (q : Qp) (v : T) :
    Timeless (PROP := IProp GF) (readGuardFrac lk q v) := by
  unfold readGuardFrac; infer_instance

theorem readGuardFrac_split (lk : Handle) (q₁ q₂ : Qp) (v : T) :
    readGuardFrac (GF := GF) lk (q₁ + q₂) v
      ⊣⊢ iprop(readGuardFrac lk q₁ v ∗ readGuardFrac lk q₂ v) := by
  unfold readGuardFrac
  exact (Fractional.fractional (Φ := fun q => pointsTo lk.data (DFrac.own q) v) q₁ q₂)

theorem isRwLock_exclusive (lk : Handle) (s₁ s₂ : LockState) (v₁ v₂ : T) :
    iprop(isRwLock lk s₁ v₁ ∗ isRwLock lk s₂ v₂) ⊢@{IProp GF} iprop(False) := by
  sorry

theorem isRwLock_agree (lk : Handle) (s₁ s₂ : LockState) (v₁ v₂ : T) :
    iprop(isRwLock lk s₁ v₁ ∗ isRwLock lk s₂ v₂) ⊢@{IProp GF} iprop(⌜s₁ = s₂ ∧ v₁ = v₂⌝) := by
  sorry

end Assertions

end AeneasIris.RwLock
