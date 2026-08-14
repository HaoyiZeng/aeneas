import AeneasIris.Lib.RwLockAPI
import AeneasIris.Effects.HeapAPI
import AeneasIris.Effects.Conc
import AeneasIris.Effects.ConcAPI
import Iris.Algebra.Auth
import Iris.Algebra.LocalUpdates
import AeneasIris.Tactics.Core
import Iris.BI.Lib.Atomic
import AeneasIris.AtomicWpi

/-! # The ITree `RwLock`: the implementation, its specs, and the instance -/

namespace AeneasIris.RwLockImpl


open Iris BI Aeneas.Data.Coinductive
open AeneasIris AeneasIris.Heap AeneasIris.HeapAPI
open Aeneas.Std (StateE StepE Loc Val RustHeap)
open scoped Aeneas.Std
open AeneasIris.Step (lat stepH)
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

/-- Agreement on the lock's data cell: a three-element discrete Leibniz CMRA. -/
inductive LocA where
  | any
  | at (c : Loc)
  | bad
deriving DecidableEq

namespace LocA

def op : LocA → LocA → LocA
  | any, y => y
  | x, any => x
  | .at a, .at b => if a = b then .at a else bad
  | _, _ => bad

@[simp] theorem op_any_left (x : LocA) : op any x = x := rfl
@[simp] theorem op_any_right (x : LocA) : op x any = x := by cases x <;> rfl

theorem op_assoc (x y z : LocA) : op x (op y z) = op (op x y) z := by
  cases x <;> cases y <;> cases z <;> simp only [op] <;> grind [op]

theorem op_comm (x y : LocA) : op x y = op y x := by
  cases x <;> cases y <;> grind [op]

instance : COFE LocA := COFE.ofDiscrete _ Eq_Equivalence
instance : OFE.Discrete LocA := ⟨congrArg id⟩
instance : OFE.Leibniz LocA := ⟨congrArg id⟩

@[simp] theorem op_self (x : LocA) : op x x = x := by cases x <;> simp [op]

instance : CMRA LocA where
  pcore x := some x
  op := op
  ValidN _ x := x ≠ bad
  Valid x := x ≠ bad
  op_ne.ne _ _ _ H := by rw [H]
  pcore_ne {_ x _ cx} H e := ⟨_, rfl, by have hx : x = cx := Option.some.inj e; exact hx ▸ H⟩
  validN_ne H := by cases H; exact id
  valid_iff_validN := .symm (forall_const _)
  validN_succ := id
  validN_op_left {_ x y} := by cases x <;> cases y <;> simp only [op] <;> grind
  assoc {x y z} := OFE.leibniz.mpr (op_assoc x y z)
  comm {x y} := OFE.leibniz.mpr (op_comm x y)
  pcore_op_left {x cx} e := by
    have hx : x = cx := Option.some.inj e
    exact hx ▸ OFE.leibniz.mpr (op_self x)
  pcore_idem _ := .rfl
  pcore_op_mono {x cx} e y := ⟨y, by have hx : x = cx := Option.some.inj e; exact hx ▸ .rfl⟩
  extend {_ x y z} := by rintro _ rfl; exists y; exists z

instance : CMRA.Discrete LocA where
  discrete_0 := id
  discrete_valid h := h

instance : UCMRA LocA where
  unit := any
  unit_valid := nofun
  unit_left_id := OFE.leibniz.mpr rfl
  pcore_unit := .rfl

instance coreId (x : LocA) : CMRA.CoreId x := ⟨.rfl⟩

@[simp] theorem cmra_op_eq (x y : LocA) : x • y = op x y := rfl

theorem loc_eq_of_incl {c d : Loc} (h : (LocA.at c : LocA) ≼ LocA.at d) : c = d := by
  obtain ⟨z, hz⟩ := h
  have hz' : (LocA.at d) = op (LocA.at c) z := hz
  rcases z with _ | e | _
  · simp only [op_any_right] at hz'; grind
  · simp only [op] at hz'; grind
  · simp only [op] at hz'; exact absurd hz' (by simp)

end LocA

/-- An outstanding reader credit, the share it holds, and the lock's data cell. -/
abbrev RwRes := ULift.{1} (Option (RwPos × RwPos) × LocA)
abbrev RwSpinF : COFE.OFunctorPre.{1,1,1} := Auth.AuthURF (constOF RwRes)

/-- The authority at data cell `c`, holding reader credit `o`. -/
def rwAuth (c : Loc) (o : Option (RwPos × RwPos)) : RwRes := ULift.up (o, .at c)

/-- A reader's credit `q` backed by share `s` of `c`. -/
def rwFragR (c : Loc) (q s : RwPos) : RwRes := ULift.up (some (q, s), .at c)

/-- The bare knowledge that the lock's data cell is `c`; duplicable. -/
def rwLocR (c : Loc) : RwRes := ULift.up (none, .at c)

instance : CMRA.CoreId (none : Option (RwPos × RwPos)) := ⟨.rfl⟩

instance (c : Loc) : CMRA.CoreId (rwLocR c) := by
  unfold rwLocR; infer_instance

/-- A reader credit cannot sit under an empty authority. -/
theorem rwFrag_not_none {c d : Loc} {q s : RwPos}
    (h : ✓ ((● (ULift.up (none, LocA.at c) : RwRes) : Auth RwRes)
              • ◯ (ULift.up (some (q, s), LocA.at d) : RwRes))) : False := by
  obtain ⟨⟨zo, zl⟩, hz⟩ := (Auth.auth_both_valid.mp h).1 0
  have h1 : (none : Option (RwPos × RwPos)) ≡{0}≡ (some (q, s)) • zo := hz.1
  cases zo <;> simp_all [CMRA.op]

theorem rwPos_ne_add (q u : RwPos) : q ≠ q + u := by
  intro h
  have h1 := congrArg RwPos.val h
  have h2 := u.pos
  simp only [RwPos.val_add] at h1
  grind

@[simp] theorem rwRes_op (o₁ o₂ : Option (RwPos × RwPos)) (l₁ l₂ : LocA) :
    (ULift.up (o₁, l₁) : RwRes) • ULift.up (o₂, l₂) = ULift.up (o₁ • o₂, l₁ • l₂) := rfl
@[simp] theorem rwOpt_op (x y : RwPos × RwPos) :
    (some x : Option (RwPos × RwPos)) • some y = some (x.1 + y.1, x.2 + y.2) := rfl
@[simp] theorem rwOpt_op_none (x : Option (RwPos × RwPos)) :
    x • (none : Option (RwPos × RwPos)) = x := by cases x <;> rfl
@[simp] theorem rwOpt_none_op (x : Option (RwPos × RwPos)) :
    (none : Option (RwPos × RwPos)) • x = x := by cases x <;> rfl

/-- Handing out a fragment: the authority grows by exactly it. -/
theorem rwAuth_alloc (a b : RwRes) (h : ✓ (b • a)) :
    (● a : Auth RwRes) ~~> ((● (b • a)) • ◯ b) := by
  refine Auth.auth_update_alloc ?_
  refine LocalUpdate.equiv_right (a, CMRA.unit)
    (y := (b • a, b • CMRA.unit)) ⟨.rfl, CMRA.unit_right_id⟩ ?_
  exact LocalUpdate.op (z := b) (fun _ _ => h.validN)

/-- Giving a fragment back, keeping only the knowledge of the data cell. -/
theorem rwAuth_release (c : Loc) (a b a' : RwRes) (hv : ✓ a')
    (h : ∀ z : RwRes, (a ≡ b • z) → (a' ≡ rwLocR c • z)) :
    ((● a : Auth RwRes) • ◯ b) ~~> ((● a') • ◯ (rwLocR c)) :=
  Auth.auth_update ((local_update_unital_discrete a b a' (rwLocR c)).mpr
    (fun z _ hz => ⟨hv, h z hz⟩))

/-- The last reader leaves: the authority is emptied. -/
theorem rwFrame_zero (c : Loc) (q s₁ s₂ : RwPos) (z : RwRes)
    (hz : (rwFragR c q s₁ : RwRes) ≡ rwFragR c q s₂ • z) :
    (rwLocR c : RwRes) ≡ rwLocR c • z := by
  obtain ⟨⟨zo, zl⟩⟩ := z
  have h0 : (rwFragR c q s₁ : RwRes) = ULift.up (some (q, s₂) • zo, LocA.at c • zl) :=
    OFE.leibniz.mp hz
  simp only [rwFragR] at h0
  injection h0 with h0
  injection h0 with h1 h2
  refine OFE.leibniz.mpr ?_
  show (ULift.up (none, LocA.at c) : RwRes) = ULift.up (none • zo, LocA.at c • zl)
  rcases zo with _ | uw
  · rw [rwOpt_none_op, ← h2]
  · exfalso
    rw [rwOpt_op] at h1
    injection h1 with h1
    injection h1 with h1 _
    exact rwPos_ne_add q uw.1 h1

/-- One of several readers leaves: the authority loses exactly its credit. -/
theorem rwFrame_succ (c : Loc) (s N Q' : RwPos) (z : RwRes)
    (hz : (rwFragR c (1 + N) (s + Q') : RwRes) ≡ rwFragR c 1 s • z) :
    (rwFragR c N Q' : RwRes) ≡ rwLocR c • z := by
  obtain ⟨⟨zo, zl⟩⟩ := z
  have h0 : (rwFragR c (1 + N) (s + Q') : RwRes)
      = ULift.up (some ((1 : RwPos), s) • zo, LocA.at c • zl) := OFE.leibniz.mp hz
  simp only [rwFragR] at h0
  injection h0 with h0
  injection h0 with h1 h2
  refine OFE.leibniz.mpr ?_
  show (ULift.up (some (N, Q'), LocA.at c) : RwRes)
      = ULift.up (none • zo, LocA.at c • zl)
  rcases zo with _ | uw
  · exfalso
    rw [rwOpt_op_none] at h1
    injection h1 with h1
    injection h1 with h1 _
    exact rwPos_ne_add 1 N h1.symm
  · rw [rwOpt_op] at h1
    injection h1 with h1
    injection h1 with ha hb
    have hu : N = uw.1 := by
      have hv1 := congrArg RwPos.val ha
      have hv2 := uw.1.pos
      simp only [RwPos.val_add, RwPos.val_one] at hv1
      exact RwPos.ext (by grind)
    have hw : Q' = uw.2 := by
      have hv1 := congrArg RwPos.val hb
      simp only [RwPos.val_add] at hv1
      exact RwPos.ext (by grind)
    rw [rwOpt_none_op, ← h2, hu, hw]

theorem RwPos.ofSucc_succ (n : Nat) : RwPos.ofSucc (n + 1) = 1 + RwPos.ofSucc n := by
  refine RwPos.ext ?_
  simp only [RwPos.ofSucc_val, RwPos.val_add, RwPos.val_one]
  push_cast
  ring

/-- A reader holding the whole credit is the only reader. -/
theorem rwIncl_last {c : Loc} {q s : RwPos}
    (h : ✓ ((● rwFragR c (1 : RwPos) q : Auth RwRes) • ◯ rwFragR c (1 : RwPos) s)) : q = s := by
  obtain ⟨⟨⟨yo, yl⟩⟩, hy⟩ := (Auth.auth_both_valid_discrete.mp h).1
  have h0 : (rwFragR c (1 : RwPos) q : RwRes)
      = ULift.up (some ((1 : RwPos), s) • yo, LocA.at c • yl) := OFE.leibniz.mp hy
  simp only [rwFragR] at h0
  injection h0 with h0
  injection h0 with h1 _
  rcases yo with _ | uw
  · rw [rwOpt_op_none] at h1
    exact congrArg Prod.snd (Option.some.inj h1)
  · exfalso
    rw [rwOpt_op] at h1
    exact rwPos_ne_add 1 uw.1 (congrArg Prod.fst (Option.some.inj h1))

/-- With other readers around, the credit splits off a positive remainder. -/
theorem rwIncl_more {c : Loc} {N q s : RwPos}
    (h : ✓ ((● rwFragR c (1 + N) q : Auth RwRes) • ◯ rwFragR c (1 : RwPos) s)) :
    ∃ Q' : RwPos, q = s + Q' := by
  obtain ⟨⟨⟨yo, yl⟩⟩, hy⟩ := (Auth.auth_both_valid_discrete.mp h).1
  have h0 : (rwFragR c (1 + N) q : RwRes)
      = ULift.up (some ((1 : RwPos), s) • yo, LocA.at c • yl) := OFE.leibniz.mp hy
  simp only [rwFragR] at h0
  injection h0 with h0
  injection h0 with h1 _
  rcases yo with _ | uw
  · exfalso
    rw [rwOpt_op_none] at h1
    exact rwPos_ne_add 1 N (congrArg Prod.fst (Option.some.inj h1)).symm
  · rw [rwOpt_op] at h1
    exact ⟨uw.2, congrArg Prod.snd (Option.some.inj h1)⟩

@[simp] theorem rwAuth_some (c : Loc) (a b : RwPos) :
    rwAuth c (some (a, b)) = rwFragR c a b := rfl
@[simp] theorem rwAuth_none (c : Loc) : rwAuth c none = rwLocR c := rfl

@[simp] theorem rwFragR_op_locR (c : Loc) (q s : RwPos) :
    rwFragR c q s • rwLocR c = rwFragR c q s := by
  simp only [rwFragR, rwLocR, rwRes_op, rwOpt_op_none, LocA.cmra_op_eq, LocA.op_self]

theorem rwFragR_op (c : Loc) (q₁ s₁ q₂ s₂ : RwPos) :
    rwFragR c q₁ s₁ • rwFragR c q₂ s₂ = rwFragR c (q₁ + q₂) (s₁ + s₂) := by
  simp only [rwFragR, rwRes_op, rwOpt_op, LocA.cmra_op_eq, LocA.op_self]

theorem rwLocR_valid (c : Loc) : ✓ (rwLocR c) := ⟨trivial, nofun⟩

theorem rwFragR_valid (c : Loc) (q s : RwPos) : ✓ (rwFragR c q s) := ⟨⟨trivial, trivial⟩, nofun⟩

/-- The authority pins the data cell any fragment names. -/
theorem rwLoc_agree {c d : Loc} {a b : Option (RwPos × RwPos)}
    (h : ✓ ((● (ULift.up (a, LocA.at c) : RwRes) : Auth RwRes)
              • ◯ (ULift.up (b, LocA.at d) : RwRes))) : d = c := by
  obtain ⟨⟨zo, zl⟩, hz⟩ := (Auth.auth_both_valid.mp h).1 0
  have h2 : (LocA.at c) = LocA.op (LocA.at d) zl := hz.2
  exact LocA.loc_eq_of_incl ⟨zl, h2⟩

class RwSpinG (GF : BundledGFunctors) where
  [rwSpinG : ElemG GF RwSpinF]

attribute [reducible, instance] RwSpinG.rwSpinG

def _root_.AeneasIris.LockState.word : LockState → Int
  | .free => 0
  | .read n => (n : Int) + 1
  | .write => -1

theorem _root_.AeneasIris.LockState.word_injective :
    Function.Injective LockState.word := by
  intro a b h
  cases a <;> cases b <;> simp_all [AeneasIris.LockState.word] <;> grind

/-- Model of `my_std::RwLock<T>`. -/
structure Handle (T : Type) where
  state : Loc
  data : Loc
deriving DecidableEq, Repr

/-- Model of `my_std::RwLockReadGuard<'_, T>`. -/
structure ReadGuard (T : Type) where
  lock : Handle T
deriving DecidableEq, Repr

/-- Model of `my_std::RwLockWriteGuard<'_, T>`. Distinct from `ReadGuard`. -/
structure WriteGuard (T : Type) where
  lock : Handle T
deriving DecidableEq, Repr

/-- The guard a successful acquire on `lk` hands back. -/
def mkReadGuard (lk : Handle T) : ReadGuard T := ⟨lk⟩

def mkWriteGuard (lk : Handle T) : WriteGuard T := ⟨lk⟩

section Code

variable {E : Effect.{1}} [StateE RustHeap.{0} -< E] [StepE.{1} -< E]
variable [Aeneas.Std.FailE.{1} -< E]
variable [Aeneas.Std.ConcE.{1} -< E]
variable {T : Type}

noncomputable def new (v : T) : ITree E (Handle T) := do
  let d ← alloc v
  let s ← alloc (0 : Int)
  return ⟨s, d⟩

noncomputable def try_read_acquire (lk : Handle T) : ITree E (Option (ReadGuard T)) := do
  let n : Int ← load lk.state
  if n < 0 then
    return none
  else
    let ok ← cas lk.state n (n + 1)
    if ok then return some ⟨lk⟩ else return none

noncomputable def try_write_acquire (lk : Handle T) : ITree E (Option (WriteGuard T)) := do
  let ok ← cas lk.state (0 : Int) (-1)
  if ok then return some ⟨lk⟩ else return none

/-! ## Acquisition and release: the synchronisation points -/

noncomputable def read_acquire (lk : Handle T) : ITree E (ReadGuard T) :=
  AeneasIris.Conc.sync (AeneasIris.Conc.waitUntil (try_read_acquire (E := E) lk))

noncomputable def write_acquire (lk : Handle T) : ITree E (WriteGuard T) :=
  AeneasIris.Conc.sync (AeneasIris.Conc.waitUntil (try_write_acquire (E := E) lk))

/-! Release does *not* yield, and the difference is not a matter of taste. -/

noncomputable def read_release (g : ReadGuard T) : ITree E Unit :=
  AeneasIris.Conc.sync <| ITree.iter (fun _ => do
    let n : Int ← load g.lock.state
    let ok ← cas g.lock.state n (n - 1)
    if ok then return .inr () else return .inl ()) ()

noncomputable def write_release (g : WriteGuard T) : ITree E Unit :=
  AeneasIris.Conc.sync (store g.lock.state (0 : Int))

noncomputable def try_read (lk : Handle T) :
    ITree E (Option (ReadGuard T × (ReadGuard T → ITree E Unit))) :=
  ITree.bind (try_read_acquire (E := E) lk)
    (fun r => .ret (r.map (fun g => (g, read_release))))

noncomputable def try_write (lk : Handle T) :
    ITree E (Option (WriteGuard T × (WriteGuard T → ITree E Unit))) :=
  ITree.bind (try_write_acquire (E := E) lk)
    (fun r => .ret (r.map (fun g => (g, write_release))))

/-- `my_std::RwLock::read`. -/
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

/-- `DerefMut for RwLockWriteGuard`. -/
noncomputable def write_deref_mut (g : WriteGuard T) :
    ITree E (T × (T → ITree E (WriteGuard T)) × (WriteGuard T → ITree E (WriteGuard T))) :=
  ITree.bind (load (E := E) g.lock.data) (fun v =>
    .ret (v, (fun w => ITree.bind (store g.lock.data w) (fun _ => .ret g)),
             (fun g' => .ret g')))

/-- `Drop for RwLockReadGuard`. -/
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

variable {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF] [G : HeapGS.{0} GF] [RwSpinG GF]
variable {T : Type}

/-- The lock's own view of the contents cell, as a function of the abstract state. -/
def rwCore (γ : GName) (c : Loc) : LockState → T → IProp GF
  | .free, v => iprop(iOwn (F := RwSpinF) γ (● rwAuth c none) ∗
      iOwn (F := RwSpinF) γ (◯ rwLocR c) ∗ c ↦ v)
  | .read n, v => iprop(
      ∃ qout qrest : Qp, ⌜qout + qrest = 1⌝ ∗
        iOwn (F := RwSpinF) γ (● rwAuth c (some (RwPos.ofSucc n, RwPos.ofQp qout))) ∗
        iOwn (F := RwSpinF) γ (◯ rwLocR c) ∗
        pointsTo c (DFrac.own qrest) v)
  | .write, _ => iprop(iOwn (F := RwSpinF) γ (● rwAuth c none) ∗
      iOwn (F := RwSpinF) γ (◯ rwLocR c))

def isRwLock (γ : GName) (lk : Handle T) (s : LockState) (v : T) : IProp GF :=
  iprop(lk.state ↦ s.word ∗ rwCore γ lk.data s v)

/-- `&mut T` is exactly the contents cell. -/
def writeGuard (γ : GName) (g : WriteGuard T) (v : T) : IProp GF :=
  iprop(g.lock.data ↦ v ∗ iOwn (F := RwSpinF) γ (◯ rwLocR g.lock.data))

/-- `&T` at client-visible strength `q`, backed by some share `s` of the cell. -/
def readGuardFrac (γ : GName) (g : ReadGuard T) (q : Qp) (v : T) : IProp GF :=
  iprop(∃ s : Qp,
    iOwn (F := RwSpinF) γ (◯ rwFragR g.lock.data (RwPos.ofQp q) (RwPos.ofQp s)) ∗
    pointsTo g.lock.data (DFrac.own s) v)

instance (γ : GName) (g : WriteGuard T) (v : T) :
    Timeless (PROP := IProp GF) (writeGuard γ g v) := by
  unfold writeGuard; infer_instance

instance rwCore_timeless (γ : GName) (c : Loc) (s : LockState) (v : T) :
    Timeless (PROP := IProp GF) (rwCore γ c s v) := by
  cases s
  · unfold rwCore; infer_instance
  · unfold rwCore
    refine @BI.exists_timeless _ _ _ _ ?_
    intro qout
    refine @BI.exists_timeless _ _ _ _ ?_
    intro qrest
    infer_instance
  · unfold rwCore; infer_instance

instance isRwLock_timeless (γ : GName) (lk : Handle T) (s : LockState) (v : T) :
    Timeless (PROP := IProp GF) (isRwLock γ lk s v) := by
  unfold isRwLock; infer_instance

instance readGuardFrac_timeless (γ : GName) (g : ReadGuard T) (q : Qp) (v : T) :
    Timeless (PROP := IProp GF) (readGuardFrac γ g q v) := by
  unfold readGuardFrac
  refine @BI.exists_timeless _ _ _ _ ?_
  intro sq
  infer_instance

private theorem rwFrag_op (c : Loc) (a b x y : RwPos) :
    rwFragR c (a + x) (b + y) = rwFragR c a b • rwFragR c x y := by
  simp only [rwFragR, rwRes_op, LocA.cmra_op_eq, LocA.op_self]
  rfl

theorem readGuardFrac_split (γ : GName) (g : ReadGuard T) (q₁ q₂ : Qp) (v : T) :
    readGuardFrac (GF := GF) γ g (q₁ + q₂) v
      ⊣⊢ iprop(readGuardFrac γ g q₁ v ∗ readGuardFrac γ g q₂ v) := by
  constructor
  · iintro H
    simp only [readGuardFrac] at *
    icases H with ⟨%s, Hown, Hpt⟩
    have hs : RwPos.ofQp s = RwPos.ofQp s.half + RwPos.ofQp s.half := by
      rw [← RwPos.ofQp_add, Qp.half_add_half]
    have hq : RwPos.ofQp (q₁ + q₂) = RwPos.ofQp q₁ + RwPos.ofQp q₂ := RwPos.ofQp_add ..
    have hpts : (pointsTo (GF := GF) g.lock.data (DFrac.own s) v : IProp GF)
        ⊢ iprop(pointsTo g.lock.data (DFrac.own s.half) v
                ∗ pointsTo g.lock.data (DFrac.own s.half) v) := by
      have h := (pointsTo_split (GF := GF) g.lock.data s.half s.half v).1
      rwa [Qp.half_add_half] at h
    simp only [hs, hq, rwFrag_op, Auth.frag_op]
    ihave Ho : iprop(iOwn (F := RwSpinF) γ
          (◯ rwFragR g.lock.data (RwPos.ofQp q₁) (RwPos.ofQp s.half))
        ∗ iOwn (F := RwSpinF) γ
          (◯ rwFragR g.lock.data (RwPos.ofQp q₂) (RwPos.ofQp s.half))) $$ [Hown]
    · iapply (BI.entails_wand iOwn_op.mp); iexact Hown
    ihave Hp : iprop(pointsTo g.lock.data (DFrac.own s.half) v
        ∗ pointsTo g.lock.data (DFrac.own s.half) v) $$ [Hpt]
    · iapply (BI.entails_wand hpts); iexact Hpt
    icases Ho with ⟨Ho1, Ho2⟩
    icases Hp with ⟨Hp1, Hp2⟩
    isplitl [Ho1 Hp1]
    · iexists s.half; isplitl [Ho1]
      · iexact Ho1
      · iexact Hp1
    · iexists s.half; isplitl [Ho2]
      · iexact Ho2
      · iexact Hp2
  · iintro ⟨H1, H2⟩
    simp only [readGuardFrac] at *
    icases H1 with ⟨%s₁, Ho1, Hp1⟩
    icases H2 with ⟨%s₂, Ho2, Hp2⟩
    iexists (s₁ + s₂)
    have hq : RwPos.ofQp (q₁ + q₂) = RwPos.ofQp q₁ + RwPos.ofQp q₂ := RwPos.ofQp_add ..
    have hs : RwPos.ofQp (s₁ + s₂) = RwPos.ofQp s₁ + RwPos.ofQp s₂ := RwPos.ofQp_add ..
    simp only [hs, hq, rwFrag_op, Auth.frag_op]
    isplitl [Ho1 Ho2]
    · iapply (BI.entails_wand iOwn_op.mpr)
      isplitl [Ho1]
      · iexact Ho1
      · iexact Ho2
    · iapply (BI.entails_wand (pointsTo_split (GF := GF) g.lock.data s₁ s₂ v).2)
      isplitl [Hp1]
      · iexact Hp1
      · iexact Hp2

/-- Two locks cannot both be described: `isRwLock` owns the counter cell. -/
theorem isRwLock_exclusive (γ : GName) (lk : Handle T) (s₁ s₂ : LockState) (v₁ v₂ : T) :
    iprop(isRwLock γ lk s₁ v₁ ∗ isRwLock γ lk s₂ v₂) ⊢@{IProp GF} iprop(False) := by
  iintro ⟨H1, H2⟩
  simp only [isRwLock] at *
  icases H1 with ⟨Hst1, _⟩
  icases H2 with ⟨Hst2, _⟩
  simp only [pointsToC] at *
  ihave %hne := ghost_map_elem_ne _ _ _ _ _ _ $$ Hst1 Hst2
  exact absurd rfl hne

/-- A read permit pins the lock to a read state. -/
theorem readGuardFrac_state (γ : GName) (lk : Handle T) (s : LockState)
    (g : ReadGuard T) (q : Qp) (v v' : T) :
    iprop(isRwLock γ lk s v ∗ readGuardFrac γ g q v') ⊢@{IProp GF} iprop(⌜∃ n, s = .read n⌝) := by
  rcases s with _ | n | _
  · iintro ⟨H1, H2⟩
    simp only [isRwLock, readGuardFrac, rwCore] at *
    icases H1 with ⟨_, Hauth, _, _⟩
    icases H2 with ⟨%sq, Hown2, _⟩
    ihave Hboth : iprop(iOwn (F := RwSpinF) γ _ ∗ iOwn (F := RwSpinF) γ _) $$ [Hauth Hown2]
    · isplitl [Hauth]
      · iexact Hauth
      · iexact Hown2
    ihave %hv := iOwn_cmraValid_op $$ Hboth
    exact (rwFrag_not_none hv).elim
  · iintro ⟨H1, H2⟩
    simp only [isRwLock, readGuardFrac, rwCore] at *
    ipureintro; exact ⟨n, rfl⟩
  · iintro ⟨H1, H2⟩
    simp only [isRwLock, readGuardFrac, rwCore] at *
    icases H1 with ⟨_, Hauth, _⟩
    icases H2 with ⟨%sq, Hown2, _⟩
    ihave Hboth : iprop(iOwn (F := RwSpinF) γ _ ∗ iOwn (F := RwSpinF) γ _) $$ [Hauth Hown2]
    · isplitl [Hauth]
      · iexact Hauth
      · iexact Hown2
    ihave %hv := iOwn_cmraValid_op $$ Hboth
    exact (rwFrag_not_none hv).elim

/-- ... and agrees with it on the contents. -/
theorem readGuardFrac_agree (γ : GName) (lk : Handle T) (s : LockState)
    (g : ReadGuard T) (q : Qp) (v v' : T) :
    iprop(isRwLock γ lk s v ∗ readGuardFrac γ g q v') ⊢@{IProp GF} iprop(⌜v = v'⌝) := by
  rcases s with _ | n | _
  · iintro ⟨H1, H2⟩
    simp only [isRwLock, readGuardFrac, rwCore] at *
    icases H1 with ⟨_, Hauth, _, _⟩
    icases H2 with ⟨%sq, Hown2, _⟩
    ihave Hboth : iprop(iOwn (F := RwSpinF) γ _ ∗ iOwn (F := RwSpinF) γ _) $$ [Hauth Hown2]
    · isplitl [Hauth]
      · iexact Hauth
      · iexact Hown2
    ihave %hv := iOwn_cmraValid_op $$ Hboth
    exact (rwFrag_not_none hv).elim
  · iintro ⟨H1, H2⟩
    simp only [isRwLock, readGuardFrac, rwCore] at *
    icases H1 with ⟨_, %qo, %qr, _, Hauth, _, Hd1⟩
    icases H2 with ⟨%sq, Hown2, Hd2⟩
    ihave Hb : iprop(iOwn (F := RwSpinF) γ _ ∗ iOwn (F := RwSpinF) γ _) $$ [Hauth Hown2]
    · isplitl [Hauth]
      · iexact Hauth
      · iexact Hown2
    ihave %hv := iOwn_cmraValid_op $$ Hb
    have hloc : g.lock.data = lk.data := rwLoc_agree hv
    simp only [hloc] at *
    ihave Hboth : iprop(pointsToC lk.data _ _ _ ∗ pointsToC lk.data _ _ _) $$ [Hd1 Hd2]
    · isplitl [Hd1]
      · iexact Hd1
      · iexact Hd2
    ihave %heq := pointsToC_agree lk.data _ _ _ _ _ _ $$ Hboth
    ipureintro
    exact Val.eq_of_Is (congrArg Prod.snd heq)
  · iintro ⟨H1, H2⟩
    simp only [isRwLock, readGuardFrac, rwCore] at *
    icases H1 with ⟨_, Hauth, _⟩
    icases H2 with ⟨%sq, Hown2, _⟩
    ihave Hboth : iprop(iOwn (F := RwSpinF) γ _ ∗ iOwn (F := RwSpinF) γ _) $$ [Hauth Hown2]
    · isplitl [Hauth]
      · iexact Hauth
      · iexact Hown2
    ihave %hv := iOwn_cmraValid_op $$ Hboth
    exact (rwFrag_not_none hv).elim

/-- A write guard pins the lock to the write state. -/
theorem writeGuard_state (γ : GName) (lk : Handle T) (s : LockState)
    (g : WriteGuard T) (v v' : T) :
    iprop(isRwLock γ lk s v ∗ writeGuard γ g v') ⊢@{IProp GF} iprop(⌜s = .write⌝) := by
  rcases s with _ | n | _
  · iintro ⟨H1, H2⟩
    simp only [isRwLock, writeGuard, rwCore] at *
    icases H1 with ⟨_, Hauth, _, Hd⟩
    icases H2 with ⟨Hgd, Hgl⟩
    ihave Hb : iprop(iOwn (F := RwSpinF) γ _ ∗ iOwn (F := RwSpinF) γ _) $$ [Hauth Hgl]
    · isplitl [Hauth]
      · iexact Hauth
      · iexact Hgl
    ihave %hv := iOwn_cmraValid_op $$ Hb
    have hloc : g.lock.data = lk.data := rwLoc_agree hv
    simp only [hloc, pointsToC] at *
    ihave %hne := ghost_map_elem_ne _ _ _ _ _ _ $$ Hgd Hd
    exact absurd rfl hne
  · iintro ⟨H1, H2⟩
    simp only [isRwLock, writeGuard, rwCore] at *
    icases H1 with ⟨_, %qo, %qr, _, Hauth, _, Hd⟩
    icases H2 with ⟨Hgd, Hgl⟩
    ihave Hb : iprop(iOwn (F := RwSpinF) γ _ ∗ iOwn (F := RwSpinF) γ _) $$ [Hauth Hgl]
    · isplitl [Hauth]
      · iexact Hauth
      · iexact Hgl
    ihave %hv := iOwn_cmraValid_op $$ Hb
    have hloc : g.lock.data = lk.data := rwLoc_agree hv
    simp only [hloc, pointsToC] at *
    ihave %hne := ghost_map_elem_ne _ _ _ _ _ _ $$ Hgd Hd
    exact absurd rfl hne
  · iintro ⟨H1, H2⟩
    simp only [isRwLock, writeGuard, rwCore] at *
    itrivial

end Assertions


open Iris BI Aeneas.Data.Coinductive
open AeneasIris AeneasIris.Heap AeneasIris.HeapAPI
open Aeneas.Std (StateE StepE Loc RustHeap RustEffect Result)
open scoped Aeneas.Std
open AeneasIris.AtomicWpi
open AeneasIris.Step (stepH)
open AeneasIris.Conc (ConcH)

section

variable {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF] [HeapGS.{0} GF] [RwSpinG GF]
variable {E : Effect.{1}} [StateE RustHeap.{0} -< E] [StepE.{1} -< E]
variable [Aeneas.Std.FailE.{1} -< E]
variable [Aeneas.Std.ConcE.{1} -< E]
variable {Hd : Handler E GF} [stateH heapInterp -<ₕ Hd]
variable {m : Mode} [stepH GF m -<ₕ Hd]

variable [ConcH GF -<ₕ Hd]
variable {T : Type}

/-! ## Allocation -/

/-- **`new`.** Mirrors `new_spec`: the lock starts free, holding `v`. -/
theorem new_spec (v : T) (M : CoPset) :
    ⦃ emp ⦄ (new (E := E) v) @ Hd ; m ; M
    ⦃ lk, ∃ γ, isRwLock γ lk .free v ⦄ := by
  show _ ⊢ _
  iintro _
  simp only [new]
  istep as ⟨d, Hdat⟩
  istep as ⟨st, Hst⟩
  have ha : ✓ (rwAuth d none) := ⟨trivial, nofun⟩
  have hb : rwLocR d ≼ rwAuth d none := ⟨ULift.up (none, LocA.any), .rfl⟩
  iapply (wpi_update (H := Hd) _ _ _).mp
  imod (iOwn_alloc (F := RwSpinF) ((● rwAuth d none : Auth RwRes) • ◯ rwLocR d)
          (Auth.auth_both_valid_2 ha hb)) with ⟨%γ, Hγ⟩
  imodintro
  ihave Hs : iprop(iOwn (F := RwSpinF) γ (● rwAuth d none)
      ∗ iOwn (F := RwSpinF) γ (◯ rwLocR d)) $$ [Hγ]
  · iapply (BI.entails_wand iOwn_op.mp); iexact Hγ
  icases Hs with ⟨Hauth, Hloc⟩
  iret
  iexists γ
  iunfold isRwLock
  isplitl [Hst]
  · simp only [LockState.word]; iexact Hst
  · iunfold rwCore
    isplitl [Hauth]
    · iexact Hauth
    · isplitl [Hloc]
      · iexact Hloc
      · iexact Hdat

/-! ## Write -/

/-- **`write_release`.** -/
theorem write_release_spec (γ : GName) (g : WriteGuard T) (v₁ : T) :
    ⊢ writeGuard γ g v₁ -∗
      ⟪ ∀ v₀, isRwLock γ g.lock .write v₀ ⟫
        Hd m (write_release (E := E) g) @ (∅ : CoPset)
      ⟪ isRwLock γ g.lock .free v₁ | RET () ⟫ := by
  iintro HG
  simp only [atomicWpi]
  iintro %Φ HAU
  simp only [write_release]
  istep
  iaupd_commit HAU as v₀ with Hlock
  iunfold isRwLock at Hlock
  icases Hlock with ⟨Hst, Hcore⟩
  simp only [LockState.word]
  istep
  iunfold rwCore at Hcore
  icases Hcore with ⟨Hauth, Hloc⟩
  iunfold writeGuard at HG
  icases HG with ⟨Hdata, _⟩
  iexists ()
  isplitl [Hst Hauth Hloc Hdata]
  · iunfold isRwLock
    isplitl [Hst]
    · simp only [LockState.word]; iexact Hst
    · iunfold rwCore
      isplitl [Hauth]
      · iexact Hauth
      · isplitl [Hloc]
        · iexact Hloc
        · iexact Hdata
  · iintro HΨ
    simp only [AtomicWpi.wandM_none]
    iapply HΨ $$ %()

/-- The compare-and-swap on its own, without the release the caller is handed.
`write_acquire` spins on this one, so it is stated separately. -/
theorem try_write_acquire_spec (γ : GName) (lk : Handle T) :
    ⊢ ⟪ ∀ s v, isRwLock γ lk s v ⟫ Hd m (try_write_acquire (E := E) lk) @ (∅ : CoPset)
        ⟪ isRwLock γ lk (if s = .free then .write else s) v
        | RET (if s = .free then some (mkWriteGuard lk) else none)
        ; if s = .free then writeGuard γ ⟨lk⟩ v else emp ⟫ := by
  simp only [atomicWpi]
  iintro %Φ HAU
  simp only [try_write_acquire]
  ibind
  iaupd_commit HAU as ⟨s, v⟩ with Hlock
  iunfold isRwLock at Hlock
  icases Hlock with ⟨Hst, Hcore⟩
  by_cases hs : s = LockState.free
  · subst hs
    simp only [LockState.word]
    istep
    iunfold rwCore at Hcore
    icases Hcore with ⟨Hauth, #Hloc, Hdata⟩
    iexists ()
    isplitl [Hst Hauth]
    · iunfold isRwLock
      isplitl [Hst]
      · simp only [if_true, LockState.word]; iexact Hst
      · simp only [if_true]; iunfold rwCore
        isplitl [Hauth]
        · iexact Hauth
        · iexact Hloc
    · iintro HΨ
      simp only [reduceIte, AtomicWpi.wandM_some]
      istep
      ihave HG : writeGuard γ ⟨lk⟩ v $$ [Hdata]
      · iunfold writeGuard
        isplitl [Hdata]
        · iexact Hdata
        · iexact Hloc
      have hite : (if LockState.free = LockState.free
                   then some (mkWriteGuard lk) else none) = some (mkWriteGuard lk) := rfl
      simp only [hite]
      simp only [mkWriteGuard]
      iapply HΨ $$ HG
      · exact ()
  · irule with HeapAPI.cas_fail_body_spec
    · iexists ()
      isplitl [Hst Hcore]
      · ihave HL : isRwLock γ lk s v $$ [Hst Hcore]
        · iunfold isRwLock
          isplitl [Hst]
          · iexact Hst
          · iexact Hcore
        have hite : (if s = LockState.free then LockState.write else s) = s :=
          if_neg hs
        have hEq : isRwLock (GF := GF) γ lk
            (if s = LockState.free then LockState.write else s) v
            = isRwLock γ lk s v := by rw [hite]
        simp only [hEq]
        iexact HL
      · iintro HΨ
        istep
        have hite : (if s = LockState.free then some (mkWriteGuard lk) else none)
                  = none := if_neg hs
        have hemp : (if s = LockState.free then writeGuard (GF := GF) γ (⟨lk⟩ : WriteGuard T) v
                     else iprop(emp)) = iprop(emp) := if_neg hs
        simp only [hite, hemp, AtomicWpi.wandM_some]
        iapply HΨ
        · first | itrivial | exact ()
        · itrivial
    · intro h
      have h2 := congrArg (fun w : Aeneas.Std.Val.{0} => Aeneas.Std.Val.unpackO Int w) h
      simp only [Aeneas.Std.Val.unpackO_pack, Option.some.injEq] at h2
      exact hs (LockState.word_injective (show s.word = LockState.free.word from h2))
theorem try_write_spec (γ : GName) (lk : Handle T) :
    ⊢ ⟪ ∀ s v, isRwLock γ lk s v ⟫ Hd m (try_write (E := E) lk) @ (∅ : CoPset)
        ⟪ isRwLock γ lk (if s = .free then .write else s) v
        | g rel, RET (if s = .free then some (g, rel) else none)
        ; if s = .free then
            writeGuard γ g v ∗
            □ (∀ v₁ : T, writeGuard γ g v₁ -∗
                 ⟪ ∀ v₀, isRwLock γ lk .write v₀ ⟫
                     Hd m (rel g) @ (∅ : CoPset)
                   ⟪ isRwLock γ lk .free v₁ | RET () ⟫)
          else emp ⟫ := by
  simp only [atomicWpi]
  iintro %Φ HAU
  simp only [try_write, try_write_acquire]
  ibind
  iaupd_commit HAU as ⟨s, v⟩ with Hlock
  iunfold isRwLock at Hlock
  icases Hlock with ⟨Hst, Hcore⟩
  by_cases hs : s = LockState.free
  · subst hs
    simp only [LockState.word]
    istep
    simp only [if_true]
    iunfold rwCore at Hcore
    icases Hcore with ⟨Hauth, #Hloc, Hdata⟩
    istep
    iexists ()
    isplitl [Hst Hauth]
    · iunfold isRwLock
      isplitl [Hst]
      · simp only [if_true, LockState.word]; iexact Hst
      · simp only [if_true]; iunfold rwCore
        isplitl [Hauth]
        · iexact Hauth
        · iexact Hloc
    · iintro HΨ
      simp only [reduceIte, AtomicWpi.wandM_some]
      istep
      ihave HG : writeGuard γ ⟨lk⟩ v $$ [Hdata]
      · iunfold writeGuard
        isplitl [Hdata]
        · iexact Hdata
        · iexact Hloc
      have hite : ∀ (y : WriteGuard T) (z : WriteGuard T → ITree E Unit),
          (if LockState.free = LockState.free then some (y, z) else none)
            = some (y, z) := fun _ _ => rfl
      simp only [Option.map_some, hite]
      iapply HΨ $$ %((⟨lk⟩ : WriteGuard T), write_release (E := E))
      isplitl [HG]
      · iexact HG
      · iintro !> %v₁ HG₁
        have HR := write_release_spec (Hd := Hd) (m := m) γ (⟨lk⟩ : WriteGuard T) v₁
        simp only [atomicWpi] at HR
        iapply HR
        iexact HG₁
  · irule with HeapAPI.cas_fail_body_spec
    · simp only [Bool.false_eq_true, if_false]
      istep
      iexists ()
      isplitl [Hst Hcore]
      · ihave HL : isRwLock γ lk s v $$ [Hst Hcore]
        · iunfold isRwLock
          isplitl [Hst]
          · iexact Hst
          · iexact Hcore
        have hite : (if s = LockState.free then LockState.write else s) = s :=
          if_neg hs
        have hEq : isRwLock (GF := GF) γ lk
            (if s = LockState.free then LockState.write else s) v
            = isRwLock γ lk s v := by rw [hite]
        simp only [hEq]
        iexact HL
      · iintro HΨ
        simp only [AtomicWpi.wandM_some]
        istep
        have hite : ∀ (y : WriteGuard T) (z : WriteGuard T → ITree E Unit),
            (if s = LockState.free then some (y, z) else none) = none :=
          fun _ _ => if_neg hs
        simp only [Option.map_none, hite]
        iapply HΨ $$ %((⟨lk⟩ : WriteGuard T), write_release (E := E))
        simp only [if_neg hs]
        itrivial
    · intro h
      have h2 := congrArg (fun w : Aeneas.Std.Val.{0} => Aeneas.Std.Val.unpackO Int w) h
      simp only [Aeneas.Std.Val.unpackO_pack, Option.some.injEq] at h2
      exact hs (LockState.word_injective (show s.word = LockState.free.word from h2))


/-- Open the update and decide to commit or abort only after seeing the state. -/
private theorem wpi_aupd_choose {A B V : Type}
    (Eo Ei Em : CoPset) (t : ITree E V)
    (α : A → IProp GF) (β Ψ : A → B → IProp GF) (Φ : Post GF V)
    (hsub : Eo ⊆ Em) :
    atomicUpdate Eo Ei α β Ψ ⊢
      iprop((∀ x, α x -∗ wpi_mask GF Hd m t
              (fun v => iprop((α x ∗ (atomicUpdate Eo Ei α β Ψ -∗ Φ v))
                              ∨ (∃ y, β x y ∗ (Ψ x y -∗ Φ v)))) Ei) -∗
            wpi_mask GF Hd m t Φ Em) := by
  iintro HAU Hbody
  iapply (AeneasIris.wpi_reduce_mask (H := Hd) t Φ Em Ei)
  imod (Iris.aupd_acc _ _ _ Eo Ei Em hsub) $$ HAU with ⟨%x, Hα, Hclose⟩
  imodintro
  iapply (AeneasIris.wpi_wand (H := Hd) t
            (fun v => iprop((α x ∗ (atomicUpdate Eo Ei α β Ψ -∗ Φ v))
                            ∨ (∃ y, β x y ∗ (Ψ x y -∗ Φ v))))
            (fun v => iprop(|={Ei, Em}=> Φ v)) Ei) $$ [Hclose]
  · iintro %v HH
    icases HH with (⟨Hα', Hret⟩ | ⟨%y, Hβ, Hret⟩)
    · icases Hclose with ⟨Habort, -⟩
      imod Habort $$ Hα' with HAU'
      imodintro
      iapply Hret $$ HAU'
    · icases Hclose with ⟨-, Hcommit⟩
      imod Hcommit $$ Hβ with HΨ
      imodintro
      iapply Hret $$ HΨ
  · iapply Hbody $$ Hα

variable [AeneasIris.Step.stepH GF .part -<ₕ Hd]

/-- **`write`.** Mirrors `write_spec`. -/
theorem write_spec (γ : GName) (lk : Handle T) :
    ⊢ ⟪ ∀ s v, isRwLock γ lk s v ⟫ Hd .part (write (E := E) lk) @ (∅ : CoPset)
        ⟪ isRwLock γ lk .write v ∗ ⌜s = .free⌝
        | g rel, RET (g, rel)
        ; writeGuard γ g v ∗
          □ (∀ v₁ : T, writeGuard γ g v₁ -∗
               ⟪ ∀ v₀, isRwLock γ lk .write v₀ ⟫ Hd .part (rel g) @ (∅ : CoPset)
                   ⟪ isRwLock γ lk .free v₁ | RET () ⟫) ⟫ := by
  simp only [atomicWpi]
  iintro %Φ HAU
  simp only [write, write_acquire]
  iapply (wpi_bind (H := Hd)
    (AeneasIris.Conc.sync (AeneasIris.Conc.waitUntil (try_write_acquire (E := E) lk))) _ _ ⊤)
  istep
  iloeb as IH
  iunfold Conc.waitUntil
  simp only [try_write_acquire]
  ibind
  iapply (wpi_aupd_choose (hsub := by aupd_mask)) $$ HAU
  iintro %iaupdPacked Hlock
  obtain ⟨s, v⟩ := iaupdPacked
  iunfold isRwLock at Hlock
  icases Hlock with ⟨Hst, Hcore⟩
  by_cases hs : s = LockState.free
  · subst hs
    simp only [LockState.word]
    istep
    simp only [if_true]
    iunfold rwCore at Hcore
    icases Hcore with ⟨Hauth, #Hloc, Hdata⟩
    istep
    iright
    iexists ()
    isplitl [Hst Hauth]
    · isplitl [Hst Hauth]
      · iunfold isRwLock
        isplitl [Hst]
        · simp only [LockState.word]; iexact Hst
        · iunfold rwCore
          isplitl [Hauth]
          · iexact Hauth
          · iexact Hloc
      · itrivial
    · iintro HΨ
      simp only [AtomicWpi.wandM_some]
      istep
      istep
      ihave HG : writeGuard γ ⟨lk⟩ v $$ [Hdata]
      · iunfold writeGuard
        isplitl [Hdata]
        · iexact Hdata
        · iexact Hloc
      iapply HΨ $$ %((⟨lk⟩ : WriteGuard T), write_release (E := E))
      isplitl [HG]
      · iexact HG
      · iintro !> %v₁ HG₁
        have HR := write_release_spec (Hd := Hd) (m := Mode.part) γ (⟨lk⟩ : WriteGuard T) v₁
        simp only [atomicWpi] at HR
        iapply HR
        iexact HG₁
  · irule with HeapAPI.cas_fail_body_spec
    · simp only [Bool.false_eq_true, if_false]
      istep
      ileft
      isplitl [Hst Hcore]
      · iunfold isRwLock
        isplitl [Hst]
        · iexact Hst
        · iexact Hcore
      · iintro HAU'
        iapply (wpi_bind (H := Hd) AeneasIris.Conc.yieldU _ _ ⊤)
        iapply (AeneasIris.Conc.wpi_yieldU (H := Hd) _)
        istep
        iapply IH $$ HAU'
    · intro h
      have h2 := congrArg (fun w : Aeneas.Std.Val.{0} => Aeneas.Std.Val.unpackO Int w) h
      simp only [Aeneas.Std.Val.unpackO_pack, Option.some.injEq] at h2
      exact hs (LockState.word_injective (show s.word = LockState.free.word from h2))

/-- What a reader holds beyond the lock: its credit and its share of the cell. -/
private def rdFrag (γ : GName) (c : Loc) (sq : Qp) (v : T) : IProp GF :=
  iprop(iOwn (F := RwSpinF) γ (◯ rwFragR c 1 (RwPos.ofQp sq)) ∗ pointsTo c (DFrac.own sq) v)

/-- Free ⇝ one reader: lock and reader take half the cell each. -/
private theorem rwAcquire_free (γ : GName) (c : Loc) (v : T) :
    iprop(rwCore γ c LockState.free v) ⊢@{IProp GF}
      iprop(|==> (∃ sq : Qp, rwCore γ c (LockState.read 0) v ∗ rdFrag γ c sq v)) := by
  iintro Hcore
  iunfold rwCore at Hcore
  icases Hcore with ⟨Hauth, #Hloc, Hdat⟩
  simp only [rwAuth_none]
  have hup : (● rwLocR c : Auth RwRes) ~~>
      ((● rwFragR c 1 (RwPos.ofQp (1 : Qp).half))
        • ◯ rwFragR c 1 (RwPos.ofQp (1 : Qp).half)) := by
    have h := rwAuth_alloc (rwLocR c) (rwFragR c 1 (RwPos.ofQp (1 : Qp).half))
      (by rw [rwFragR_op_locR]; exact rwFragR_valid _ _ _)
    rwa [rwFragR_op_locR] at h
  imod (iOwn_update (F := RwSpinF) (γ := γ) hup) $$ [Hauth] with Hnew
  · iexact Hauth
  imodintro
  ihave Hpair : iprop(iOwn (F := RwSpinF) γ (● rwFragR c 1 (RwPos.ofQp (1 : Qp).half))
      ∗ iOwn (F := RwSpinF) γ (◯ rwFragR c 1 (RwPos.ofQp (1 : Qp).half))) $$ [Hnew]
  · iapply (BI.entails_wand iOwn_op.mp); iexact Hnew
  icases Hpair with ⟨Hauth2, Hfrag⟩
  ihave Hd2 : iprop(pointsTo c (DFrac.own (1 : Qp).half) v
      ∗ pointsTo c (DFrac.own (1 : Qp).half) v) $$ [Hdat]
  · have hh := (pointsTo_split (GF := GF) c (1 : Qp).half (1 : Qp).half v).1
    rw [Qp.half_add_half] at hh
    iapply (BI.entails_wand hh); iexact Hdat
  icases Hd2 with ⟨Hd2a, Hd2b⟩
  iexists (1 : Qp).half
  isplitl [Hauth2 Hd2a]
  · iunfold rwCore
    simp only [rwAuth_some, RwPos.ofSucc_zero]
    iexists (1 : Qp).half
    iexists (1 : Qp).half
    isplitr [Hauth2 Hd2a]
    · ipureintro; exact Qp.half_add_half 1
    · isplitl [Hauth2]
      · iexact Hauth2
      · isplitr [Hd2a]
        · iexact Hloc
        · iexact Hd2a
  · iunfold rdFrag
    isplitl [Hfrag]
    · iexact Hfrag
    · iexact Hd2b

/-- One more reader: the newcomer takes half of what the lock still holds. -/
private theorem rwAcquire_read (γ : GName) (c : Loc) (m : Nat) (v : T) :
    iprop(rwCore γ c (LockState.read m) v) ⊢@{IProp GF}
      iprop(|==> (∃ sq : Qp, rwCore γ c (LockState.read (m + 1)) v ∗ rdFrag γ c sq v)) := by
  iintro Hcore
  iunfold rwCore at Hcore
  icases Hcore with ⟨%qout, %qrest, %hsum, Hauth, #Hloc, Hdat⟩
  simp only [rwAuth_some]
  have hb : rwFragR c 1 (RwPos.ofQp qrest.half) • rwFragR c (RwPos.ofSucc m) (RwPos.ofQp qout)
      = rwFragR c (RwPos.ofSucc (m + 1)) (RwPos.ofQp (qout + qrest.half)) := by
    rw [rwFragR_op]
    have h1 : (1 : RwPos) + RwPos.ofSucc m = RwPos.ofSucc (m + 1) := (RwPos.ofSucc_succ m).symm
    have h2 : RwPos.ofQp qrest.half + RwPos.ofQp qout = RwPos.ofQp (qout + qrest.half) :=
      RwPos.ext (by simp only [RwPos.val_add, RwPos.ofQp_val, Qp.val_add]; grind)
    rw [h1, h2]
  have hup : (● rwFragR c (RwPos.ofSucc m) (RwPos.ofQp qout) : Auth RwRes) ~~>
      ((● rwFragR c (RwPos.ofSucc (m + 1)) (RwPos.ofQp (qout + qrest.half)))
        • ◯ rwFragR c 1 (RwPos.ofQp qrest.half)) := by
    have h := rwAuth_alloc (rwFragR c (RwPos.ofSucc m) (RwPos.ofQp qout))
      (rwFragR c 1 (RwPos.ofQp qrest.half)) (by rw [hb]; exact rwFragR_valid _ _ _)
    rwa [hb] at h
  imod (iOwn_update (F := RwSpinF) (γ := γ) hup) $$ [Hauth] with Hnew
  · iexact Hauth
  imodintro
  ihave Hpair : iprop(iOwn (F := RwSpinF) γ
        (● rwFragR c (RwPos.ofSucc (m + 1)) (RwPos.ofQp (qout + qrest.half)))
      ∗ iOwn (F := RwSpinF) γ (◯ rwFragR c 1 (RwPos.ofQp qrest.half))) $$ [Hnew]
  · iapply (BI.entails_wand iOwn_op.mp); iexact Hnew
  icases Hpair with ⟨Hauth2, Hfrag⟩
  ihave Hd2 : iprop(pointsTo c (DFrac.own qrest.half) v
      ∗ pointsTo c (DFrac.own qrest.half) v) $$ [Hdat]
  · have hh := (pointsTo_split (GF := GF) c qrest.half qrest.half v).1
    rw [Qp.half_add_half] at hh
    iapply (BI.entails_wand hh); iexact Hdat
  icases Hd2 with ⟨Hd2a, Hd2b⟩
  have hsum2 : (qout + qrest.half) + qrest.half = (1 : Qp) := by
    simp only [Qp.ext_iff, Qp.val_add, Qp.val_one] at *
    grind
  iexists qrest.half
  isplitl [Hauth2 Hd2a]
  · iunfold rwCore
    simp only [rwAuth_some]
    iexists (qout + qrest.half)
    iexists qrest.half
    isplitr [Hauth2 Hd2a]
    · ipureintro; exact hsum2
    · isplitl [Hauth2]
      · iexact Hauth2
      · isplitr [Hd2a]
        · iexact Hloc
        · iexact Hd2a
  · iunfold rdFrag
    isplitl [Hfrag]
    · iexact Hfrag
    · iexact Hd2b

/-- The last reader releasing: the lock empties, and the shares must agree. -/
private theorem rwRelease_last (γ : GName) (c : Loc) (Y s : RwPos) :
    iprop(iOwn (F := RwSpinF) γ (● rwFragR c 1 Y) ∗ iOwn (F := RwSpinF) γ (◯ rwFragR c 1 s))
      ⊢@{IProp GF} iprop(|==> (⌜Y = s⌝ ∗ iOwn (F := RwSpinF) γ (● rwLocR c)
                  ∗ iOwn (F := RwSpinF) γ (◯ rwLocR c))) := by
  refine (BI.and_intro iOwn_cmraValid_op .rfl).trans (BI.persistent_and_sep_mp.trans ?_)
  iintro ⟨%hv, H⟩
  ihave Hupd : iprop(|==> iOwn (F := RwSpinF) γ ((● rwLocR c : Auth RwRes) • ◯ rwLocR c)) $$ [H]
  · iapply (BI.entails_wand (iOwn_update_op
      (rwAuth_release c (rwFragR c 1 Y) (rwFragR c 1 s) (rwLocR c) (rwLocR_valid c)
        (rwFrame_zero c 1 Y s))))
    iexact H
  imod Hupd with H2
  imodintro
  isplitr [H2]
  · ipureintro; exact rwIncl_last hv
  · iapply (BI.entails_wand iOwn_op.mp); iexact H2

/-- One of several readers releasing: the credit shrinks by exactly its own. -/
private theorem rwRelease_more (γ : GName) (c : Loc) (N Y s : RwPos) :
    iprop(iOwn (F := RwSpinF) γ (● rwFragR c (1 + N) Y)
        ∗ iOwn (F := RwSpinF) γ (◯ rwFragR c 1 s))
      ⊢@{IProp GF} iprop(|==> (∃ Q' : RwPos, ⌜Y = s + Q'⌝ ∗ iOwn (F := RwSpinF) γ (● rwFragR c N Q')
                  ∗ iOwn (F := RwSpinF) γ (◯ rwLocR c))) := by
  refine (BI.and_intro iOwn_cmraValid_op .rfl).trans (BI.persistent_and_sep_mp.trans ?_)
  iintro ⟨%hv, H⟩
  obtain ⟨Q', hQ⟩ := rwIncl_more hv
  subst hQ
  ihave Hupd : iprop(|==> iOwn (F := RwSpinF) γ
      ((● rwFragR c N Q' : Auth RwRes) • ◯ rwLocR c)) $$ [H]
  · iapply (BI.entails_wand (iOwn_update_op
      (rwAuth_release c (rwFragR c (1 + N) (s + Q')) (rwFragR c 1 s) (rwFragR c N Q')
        (rwFragR_valid c N Q') (rwFrame_succ c s N Q'))))
    iexact H
  imod Hupd with H2
  imodintro
  iexists Q'
  isplitr [H2]
  · ipureintro; rfl
  · iapply (BI.entails_wand iOwn_op.mp); iexact H2

/-- **`read_release`.** The counterpart of `write_release`, for the same reason. -/
theorem read_release_spec (γ : GName) (g : ReadGuard T) (v : T) :
    ⊢ readGuardFrac γ g 1 v -∗
      ⟪ ∀ s, isRwLock γ g.lock s v ⟫
        Hd .part (read_release (E := E) g) @ (∅ : CoPset)
      ⟪ (isRwLock γ g.lock .free v ∗ ⌜s = .read 0⌝) ∨
        (∃ n : Nat, isRwLock γ g.lock (.read n) v ∗ ⌜s = .read (n + 1)⌝)
      | RET () ⟫ := by
  iintro HR
  simp only [atomicWpi]
  iintro %Φ HAU
  simp only [read_release]
  istep
  iunfold ITree.iter
  ibind
  iapply (wpi_aupd_choose (hsub := by aupd_mask)) $$ HAU
  iintro %s₁ Hlock
  rcases s₁ with _ | m | _
  · ihave Hpair : iprop(isRwLock γ g.lock LockState.free v ∗ readGuardFrac γ g 1 v) $$ [Hlock HR]
    · isplitl [Hlock]
      · iexact Hlock
      · iexact HR
    ihave %hbad := readGuardFrac_state γ g.lock LockState.free g 1 v v $$ Hpair
    exact absurd hbad (by rintro ⟨k, hk⟩; cases hk)
  · iunfold isRwLock at Hlock
    icases Hlock with ⟨Hst, Hcore⟩
    iunfold rwCore at Hcore
    icases Hcore with ⟨%qout, %qrest, %hsum, Hauth, #Hloc, Hdat⟩
    iunfold readGuardFrac at HR
    icases HR with ⟨%sh, Hfrag, Hdr⟩
    istep
    istep
    rcases m with _ | k
    · simp only [rwAuth_some, RwPos.ofSucc_zero, RwPos.ofQp_one] at *
      iapply (wpi_update (H := Hd) _ _ _).mp
      imod (rwRelease_last γ g.lock.data (RwPos.ofQp qout) (RwPos.ofQp sh)) $$ [Hauth Hfrag]
        with ⟨%hqs, Hauth2, Hloc2⟩
      · isplitl [Hauth]
        · iexact Hauth
        · iexact Hfrag
      imodintro
      have hq : qout = sh := RwPos.ofQp_inj hqs
      have hfr : qrest + sh = (1 : Qp) := by
        subst hq
        simp only [Qp.ext_iff, Qp.val_add, Qp.val_one] at *
        grind
      ihave Hfull : iprop(pointsTo g.lock.data (DFrac.own (1 : Qp)) v) $$ [Hdat Hdr]
      · simp only [← hfr]
        iapply (BI.entails_wand (pointsTo_split (GF := GF) g.lock.data qrest sh v).2)
        isplitl [Hdat]
        · iexact Hdat
        · iexact Hdr
      simp only [if_true]
      istep
      iright
      iexists ()
      isplitl [Hst Hauth2 Hloc2 Hfull]
      · ileft
        isplitl [Hst Hauth2 Hloc2 Hfull]
        · iunfold isRwLock
          isplitl [Hst]
          · simp only [LockState.word] at *
            have hw0 : ((0 : Nat) : Int) + 1 - 1 = (0 : Int) := by grind
            simp only [hw0]
            iexact Hst
          · iunfold rwCore
            simp only [rwAuth_none]
            isplitl [Hauth2]
            · iexact Hauth2
            · isplitl [Hloc2]
              · iexact Hloc2
              · iexact Hfull
        · itrivial
      · iintro HΨ
        simp only [AtomicWpi.wandM_none]
        istep
        iapply HΨ $$ %()
    · simp only [rwAuth_some, RwPos.ofSucc_succ, RwPos.ofQp_one] at *
      iapply (wpi_update (H := Hd) _ _ _).mp
      imod (rwRelease_more γ g.lock.data (RwPos.ofSucc k) (RwPos.ofQp qout) (RwPos.ofQp sh))
        $$ [Hauth Hfrag] with ⟨%Q', %hqs, Hauth2, Hloc2⟩
      · isplitl [Hauth]
        · iexact Hauth
        · iexact Hfrag
      imodintro
      have hQpos : (0 : Rat) < Q'.val := Q'.pos
      have hfr : (⟨Q'.val, hQpos⟩ : Qp) + (qrest + sh) = (1 : Qp) := by
        have h1 := congrArg RwPos.val hqs
        simp only [RwPos.ofQp_val, RwPos.val_add] at h1
        simp only [Qp.ext_iff, Qp.val_add, Qp.val_one] at *
        grind
      ihave Hrest : iprop(pointsTo g.lock.data (DFrac.own (qrest + sh)) v) $$ [Hdat Hdr]
      · iapply (BI.entails_wand (pointsTo_split (GF := GF) g.lock.data qrest sh v).2)
        isplitl [Hdat]
        · iexact Hdat
        · iexact Hdr
      simp only [if_true]
      istep
      iright
      iexists ()
      isplitl [Hst Hauth2 Hloc2 Hrest]
      · iright
        iexists k
        isplitl [Hst Hauth2 Hloc2 Hrest]
        · iunfold isRwLock
          isplitl [Hst]
          · simp only [LockState.word] at *
            push_cast at *
            have hwk : ((k : Nat) : Int) + 1 + 1 - 1 = ((k : Nat) : Int) + 1 := by grind
            simp only [hwk]
            iexact Hst
          · iunfold rwCore
            have hQ' : RwPos.ofQp (⟨Q'.val, hQpos⟩ : Qp) = Q' := RwPos.ext rfl
            simp only [rwAuth_some]
            iexists (⟨Q'.val, hQpos⟩ : Qp)
            iexists (qrest + sh)
            isplitr [Hauth2 Hloc2 Hrest]
            · ipureintro; exact hfr
            · isplitl [Hauth2]
              · simp only [hQ']
                iexact Hauth2
              · isplitl [Hloc2]
                · iexact Hloc2
                · iexact Hrest
        · itrivial
      · iintro HΨ
        simp only [AtomicWpi.wandM_none]
        istep
        iapply HΨ $$ %()
  · ihave Hpair : iprop(isRwLock γ g.lock LockState.write v ∗ readGuardFrac γ g 1 v) $$ [Hlock HR]
    · isplitl [Hlock]
      · iexact Hlock
      · iexact HR
    ihave %hbad := readGuardFrac_state γ g.lock LockState.write g 1 v v $$ Hpair
    exact absurd hbad (by rintro ⟨k, hk⟩; cases hk)

/-! ## Read -/

/-- `try_read_acquire` from the free state, with an abstract continuation.

Split off as its own declaration because the three states cannot share one
heartbeat budget: each does a machine step, a CAS and a ghost update. -/
private theorem try_read_acquire_free (γ : GName) (lk : Handle T) (v : T)
    (Ψ : Post GF (Option (ReadGuard T))) :
    iprop(lk.state ↦ LockState.free.word ∗ rwCore γ lk.data LockState.free v ∗
      (∀ sq : Qp, (isRwLock γ lk (LockState.read 0) v ∗ rdFrag γ lk.data sq v) -∗
        Ψ (some (⟨lk⟩ : ReadGuard T))))
    ⊢@{IProp GF} wpi_mask GF Hd m (try_read_acquire (E := E) lk) Ψ ∅ := by
  iintro ⟨Hst, Hcore, Hk⟩
  simp only [try_read_acquire, LockState.word]
  istep
  simp only [lt_self_iff_false, if_false]
  istep
  iapply (wpi_update (H := Hd) _ _ _).mp
  imod (rwAcquire_free γ lk.data v) $$ [Hcore] with ⟨%sq, Hcore2, Hfrag⟩
  · iexact Hcore
  imodintro
  simp only [if_true]
  istep
  have hw : (LockState.read 0).word = (0 : Int) + 1 := by
    simp only [LockState.word]; grind
  iapply Hk $$ %sq
  isplitr [Hfrag]
  · iunfold isRwLock
    simp only [hw]
    iframe
  · iexact Hfrag

/-- `try_read_acquire` from a read state. -/
private theorem try_read_acquire_read (γ : GName) (lk : Handle T) (k : Nat) (v : T)
    (Ψ : Post GF (Option (ReadGuard T))) :
    iprop(lk.state ↦ (LockState.read k).word ∗ rwCore γ lk.data (LockState.read k) v ∗
      (∀ sq : Qp, (isRwLock γ lk (LockState.read (k + 1)) v ∗ rdFrag γ lk.data sq v) -∗
        Ψ (some (⟨lk⟩ : ReadGuard T))))
    ⊢@{IProp GF} wpi_mask GF Hd m (try_read_acquire (E := E) lk) Ψ ∅ := by
  have hnn : ¬ (((k : Nat) : Int) + 1 < 0) := by
    have h0 : (0 : Int) ≤ ((k : Nat) : Int) := by simp
    grind
  iintro ⟨Hst, Hcore, Hk⟩
  simp only [try_read_acquire, LockState.word]
  istep
  simp only [eq_false hnn, if_false]
  istep
  iapply (wpi_update (H := Hd) _ _ _).mp
  imod (rwAcquire_read γ lk.data k v) $$ [Hcore] with ⟨%sq, Hcore2, Hfrag⟩
  · iexact Hcore
  imodintro
  simp only [if_true]
  istep
  iapply Hk $$ %sq
  isplitr [Hfrag]
  · iunfold isRwLock
    simp only [LockState.word]
    push_cast
    iframe
  · iexact Hfrag

/-- `try_read_acquire` from the write state: it gives up. -/
private theorem try_read_acquire_write (γ : GName) (lk : Handle T) (v : T)
    (Ψ : Post GF (Option (ReadGuard T))) :
    iprop(lk.state ↦ LockState.write.word ∗ rwCore γ lk.data LockState.write v ∗
      (isRwLock γ lk LockState.write v -∗ Ψ none))
    ⊢@{IProp GF} wpi_mask GF Hd m (try_read_acquire (E := E) lk) Ψ ∅ := by
  iintro ⟨Hst, Hcore, Hk⟩
  simp only [try_read_acquire, LockState.word]
  istep
  have hpos : ((-1 : Int) < 0) := by decide
  simp only [if_pos hpos]
  istep
  iapply Hk
  iunfold isRwLock
  simp only [LockState.word]
  iframe

/-- The release box every read acquire hands back, elaborated once. -/
private theorem read_release_box (γ : GName) (lk : Handle T) (v : T) :
    ⊢@{IProp GF} □ (readGuardFrac γ (⟨lk⟩ : ReadGuard T) 1 v -∗
      ⟪ ∀ s', isRwLock γ lk s' v ⟫
          Hd .part (read_release (E := E) (⟨lk⟩ : ReadGuard T)) @ (∅ : CoPset)
        ⟪ (isRwLock γ lk .free v ∗ ⌜s' = .read 0⌝) ∨
          (∃ n : Nat, isRwLock γ lk (.read n) v ∗ ⌜s' = .read (n + 1)⌝)
        | RET () ⟫) := by
  iintro !> HRG
  have HRR := read_release_spec (Hd := Hd) γ (⟨lk⟩ : ReadGuard T) v
  iapply HRR
  iexact HRG

/-- **`try_read`.** Mirrors `try_read_spec`. -/
theorem try_read_spec (γ : GName) (lk : Handle T) :
    ⊢ ⟪ ∀ s v, isRwLock γ lk s v ⟫ Hd m (try_read (E := E) lk) @ (∅ : CoPset)
        ⟪ isRwLock γ lk (match s with
                         | .free => .read 0
                         | .read n => .read (n + 1)
                         | .write => .write) v
        | g rel, RET (if s = .write then none else some (g, rel))
        ; if s = .write then emp else
            readGuardFrac γ g 1 v ∗
            □ (readGuardFrac γ g 1 v -∗
                 ⟪ ∀ s', isRwLock γ lk s' v ⟫
                     Hd .part (rel g) @ (∅ : CoPset)
                   ⟪ (isRwLock γ lk .free v ∗ ⌜s' = .read 0⌝) ∨
                     (∃ n : Nat, isRwLock γ lk (.read n) v ∗ ⌜s' = .read (n + 1)⌝)
                   | RET () ⟫) ⟫ := by
  rw [atomicWpi]
  iintro %Φ HAU
  simp only [try_read]
  ibind
  iapply (wpi_aupd_choose (hsub := by aupd_mask)) $$ HAU
  iintro %iaupdPacked Hlock
  obtain ⟨(_ | k | _), v⟩ := iaupdPacked
  · iunfold isRwLock at Hlock
    icases Hlock with ⟨Hst, Hcore⟩
    iapply (BI.entails_wand (try_read_acquire_free γ lk v _))
    isplitl [Hst]
    · iexact Hst
    · isplitl [Hcore]
      · iexact Hcore
      · iintro %sq ⟨HL, HF⟩
        iright
        iexists ()
        isplitl [HL]
        · iexact HL
        · iintro HΨ
          have hne1 : ∀ (y : ReadGuard T) (z : ReadGuard T → ITree E Unit),
              (if LockState.free = LockState.write then none else some (y, z)) = some (y, z) :=
            fun _ _ => if_neg (by intro h; cases h)
          have hne2 : ∀ P : IProp GF,
              (if LockState.free = LockState.write then iprop(emp) else P) = P :=
            fun _ => if_neg (by intro h; cases h)
          simp only [hne1, hne2, Option.map_some, AtomicWpi.wandM_some]
          istep
          iapply HΨ $$ %((⟨lk⟩ : ReadGuard T), read_release (E := E))
          isplitl [HF]
          · iunfold readGuardFrac
            iexists sq
            simp only [RwPos.ofQp_one]
            iunfold rdFrag at HF
            iexact HF
          · iapply (BI.entails_wand (read_release_box (Hd := Hd) γ lk v))
            itrivial
  · iunfold isRwLock at Hlock
    icases Hlock with ⟨Hst, Hcore⟩
    iapply (BI.entails_wand (try_read_acquire_read γ lk k v _))
    isplitl [Hst]
    · iexact Hst
    · isplitl [Hcore]
      · iexact Hcore
      · iintro %sq ⟨HL, HF⟩
        iright
        iexists ()
        isplitl [HL]
        · iexact HL
        · iintro HΨ
          have hne1 : ∀ (y : ReadGuard T) (z : ReadGuard T → ITree E Unit),
              (if LockState.read k = LockState.write then none else some (y, z)) = some (y, z) :=
            fun _ _ => if_neg (by intro h; cases h)
          have hne2 : ∀ P : IProp GF,
              (if LockState.read k = LockState.write then iprop(emp) else P) = P :=
            fun _ => if_neg (by intro h; cases h)
          simp only [hne1, hne2, Option.map_some, AtomicWpi.wandM_some]
          istep
          iapply HΨ $$ %((⟨lk⟩ : ReadGuard T), read_release (E := E))
          isplitl [HF]
          · iunfold readGuardFrac
            iexists sq
            simp only [RwPos.ofQp_one]
            iunfold rdFrag at HF
            iexact HF
          · iapply (BI.entails_wand (read_release_box (Hd := Hd) γ lk v))
            itrivial
  · iunfold isRwLock at Hlock
    icases Hlock with ⟨Hst, Hcore⟩
    iapply (BI.entails_wand (try_read_acquire_write γ lk v _))
    isplitl [Hst]
    · iexact Hst
    · isplitl [Hcore]
      · iexact Hcore
      · iintro HL
        iright
        iexists ()
        isplitl [HL]
        · iexact HL
        · iintro HΨ
          have heq1 : ∀ (y : ReadGuard T) (z : ReadGuard T → ITree E Unit),
              (if LockState.write = LockState.write then
                 (none : Option (ReadGuard T × (ReadGuard T → ITree E Unit)))
               else some (y, z)) = none := fun _ _ => if_pos rfl
          have heq2 : ∀ P : IProp GF,
              (if LockState.write = LockState.write then iprop(emp) else P) = iprop(emp) :=
            fun _ => if_pos rfl
          simp only [heq1, Option.map_none, AtomicWpi.wandM_some]
          istep
          iapply HΨ $$ %((⟨lk⟩ : ReadGuard T), read_release (E := E))
          itrivial

theorem read_spec (γ : GName) (lk : Handle T) :
    ⊢ ⟪ ∀ s v, isRwLock γ lk s v ⟫ Hd .part (read (E := E) lk) @ (∅ : CoPset)
        ⟪ (isRwLock γ lk (.read 0) v ∗ ⌜s = .free⌝) ∨
          (∃ k : Nat, isRwLock γ lk (.read (k + 1)) v ∗ ⌜s = .read k⌝)
        | g rel, RET (g, rel)
        ; readGuardFrac γ g 1 v ∗
          □ (readGuardFrac γ g 1 v -∗
               ⟪ ∀ s', isRwLock γ lk s' v ⟫ Hd .part (rel g) @ (∅ : CoPset)
                   ⟪ (isRwLock γ lk .free v ∗ ⌜s' = .read 0⌝) ∨
                     (∃ n : Nat, isRwLock γ lk (.read n) v ∗ ⌜s' = .read (n + 1)⌝)
                   | RET () ⟫) ⟫ := by
  rw [atomicWpi]
  iintro %Φ HAU
  simp only [read, read_acquire]
  iapply (wpi_bind (H := Hd)
    (AeneasIris.Conc.sync (AeneasIris.Conc.waitUntil (try_read_acquire (E := E) lk))) _ _ ⊤)
  istep
  iloeb as IH
  iunfold Conc.waitUntil
  ibind
  iapply (wpi_aupd_choose (hsub := by aupd_mask)) $$ HAU
  iintro %iaupdPacked Hlock
  obtain ⟨(_ | k | _), v⟩ := iaupdPacked
  · iunfold isRwLock at Hlock
    icases Hlock with ⟨Hst, Hcore⟩
    iapply (BI.entails_wand (try_read_acquire_free γ lk v _))
    isplitl [Hst]
    · iexact Hst
    · isplitl [Hcore]
      · iexact Hcore
      · iintro %sq ⟨HL, HF⟩
        iright
        iexists ()
        isplitl [HL]
        · ileft
          isplitl [HL]
          · iexact HL
          · itrivial
        · iintro HΨ
          simp only [AtomicWpi.wandM_some]
          istep
          istep
          iapply HΨ $$ %((⟨lk⟩ : ReadGuard T), read_release (E := E))
          isplitl [HF]
          · iunfold readGuardFrac
            iexists sq
            simp only [RwPos.ofQp_one]
            iunfold rdFrag at HF
            iexact HF
          · iapply (BI.entails_wand (read_release_box (Hd := Hd) γ lk v))
            itrivial
  · iunfold isRwLock at Hlock
    icases Hlock with ⟨Hst, Hcore⟩
    iapply (BI.entails_wand (try_read_acquire_read γ lk k v _))
    isplitl [Hst]
    · iexact Hst
    · isplitl [Hcore]
      · iexact Hcore
      · iintro %sq ⟨HL, HF⟩
        iright
        iexists ()
        isplitl [HL]
        · iright
          iexists k
          isplitl [HL]
          · iexact HL
          · itrivial
        · iintro HΨ
          simp only [AtomicWpi.wandM_some]
          istep
          istep
          iapply HΨ $$ %((⟨lk⟩ : ReadGuard T), read_release (E := E))
          isplitl [HF]
          · iunfold readGuardFrac
            iexists sq
            simp only [RwPos.ofQp_one]
            iunfold rdFrag at HF
            iexact HF
          · iapply (BI.entails_wand (read_release_box (Hd := Hd) γ lk v))
            itrivial
  · iunfold isRwLock at Hlock
    icases Hlock with ⟨Hst, Hcore⟩
    iapply (BI.entails_wand (try_read_acquire_write γ lk v _))
    isplitl [Hst]
    · iexact Hst
    · isplitl [Hcore]
      · iexact Hcore
      · iintro HL
        ileft
        isplitl [HL]
        · iexact HL
        · iintro HAU'
          iapply (wpi_bind (H := Hd) AeneasIris.Conc.yieldU _ _ ⊤)
          iapply (AeneasIris.Conc.wpi_yieldU (H := Hd) _)
          istep
          iapply IH $$ HAU'

/-! ## Dereference -/

/-- **`write_deref`.** -/
theorem write_deref_spec (γ : GName) (g : WriteGuard T) (v : T) (M : CoPset) :
    ⦃ writeGuard γ g v ⦄ (write_deref (E := E) g) @ Hd ; m ; M
    ⦃ r, ⌜r = v⌝ ∗ writeGuard γ g v ⦄ := by
  show _ ⊢ _
  iintro Hd
  simp only [writeGuard] at *
  icases Hd with ⟨Hd, Hl⟩
  simp only [write_deref]
  istep
  isplitr
  itrivial
  iframe

/-- **`read_deref`.** -/
theorem read_deref_spec (γ : GName) (g : ReadGuard T) (q : Qp) (v : T) (M : CoPset) :
    ⦃ readGuardFrac γ g q v ⦄ (read_deref (E := E) g) @ Hd ; m ; M
    ⦃ r, ⌜r = v⌝ ∗ readGuardFrac γ g q v ⦄ := by
  show _ ⊢ _
  iintro HR
  simp only [readGuardFrac] at *
  icases HR with ⟨%sh, Hown, Hpt⟩
  simp only [read_deref]
  istep
  isplitr
  itrivial
  iexists sh
  iframe

/-- **`write_deref_mut`.** Mirrors `write_deref_mut_spec`. -/
theorem write_deref_mut_spec (γ : GName) (g : WriteGuard T) (v : T) (M : CoPset) :
    ⦃ writeGuard γ g v ⦄ (write_deref_mut (E := E) g) @ Hd ; m ; M
    ⦃ r, ∃ set back, ⌜r = (v, set, back)⌝ ∗
        writeGuard γ g v ∗
        □ (∀ v₀ : T, ∀ v' : T, writeGuard γ g v₀ -∗
             wpi_mask GF Hd m (set v')
               (fun g' => iprop(⌜g' = g⌝ ∗ writeGuard γ g v')) ⊤) ⦄ := by
  show _ ⊢ _
  iintro Hd
  simp only [writeGuard] at *
  icases Hd with ⟨Hd, Hl⟩
  simp only [write_deref_mut]
  istep
  iret
  iexists (fun w => ITree.bind (store g.lock.data w) (fun _ => ITree.ret g))
  iexists (fun g' => ITree.ret g')
  isplitr
  itrivial
  isplitl [Hd Hl]
  · iframe
  · iintro !> %v₀ %v' Hd
    simp only []
    icases Hd with ⟨Hd, Hl'⟩
    istep
    istep
    isplitr
    itrivial
    iframe

theorem drop_spec (γ : GName) (lk : Handle T) (v : T) (M : CoPset) :
    ⦃ isRwLock γ lk .free v ⦄ (drop (E := E) lk) @ Hd ; m ; M
    ⦃ r, ⌜r = ()⌝ ⦄ := by
  show _ ⊢ _
  iintro HL
  simp only [isRwLock, rwCore] at *
  icases HL with ⟨Hst, Hauth, Hloc, Hdata⟩
  simp only [drop]
  istep
  istep
  itrivial

/-! ## The instance

Every field is one of the definitions or theorems above; nothing is proved here.
-/

noncomputable instance instRwLockAPI : RwLockAPI GF Hd m where
  RwLock := Handle
  ReadGuard := ReadGuard
  WriteGuard := WriteGuard

  new := new
  drop := drop
  try_read := try_read
  try_write := try_write
  read := read
  write := write
  read_deref := read_deref
  write_deref := write_deref
  write_deref_mut := write_deref_mut

  isRwLock := isRwLock
  writeGuard := writeGuard
  readGuardFrac := readGuardFrac

  isRwLock_timeless := by infer_instance
  writeGuard_timeless := by infer_instance
  readGuardFrac_timeless := by infer_instance

  isRwLock_exclusive := isRwLock_exclusive
  readGuardFrac_split := readGuardFrac_split
  readGuardFrac_state := readGuardFrac_state
  readGuardFrac_agree := readGuardFrac_agree
  writeGuard_state := writeGuard_state

  new_spec := new_spec
  drop_spec := drop_spec
  try_write_spec := try_write_spec
  write_spec := write_spec
  try_read_spec := try_read_spec
  read_spec := read_spec
  write_deref_spec := write_deref_spec
  read_deref_spec := read_deref_spec
  write_deref_mut_spec := write_deref_mut_spec

end


end AeneasIris.RwLockImpl
