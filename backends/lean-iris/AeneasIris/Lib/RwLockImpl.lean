import AeneasIris.Lib.RwLockAPI
import AeneasIris.Effects.HeapAPI
import AeneasIris.Effects.Conc
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
open AeneasIris.RwLockAPI (LockState)

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

/-- The resource: an outstanding reader credit and the share it holds. -/
abbrev RwRes := ULift.{1} (Option (RwPos × RwPos))
abbrev RwSpinF : COFE.OFunctorPre.{1,1,1} := Auth.AuthURF (constOF RwRes)

class RwSpinG (GF : BundledGFunctors) where
  [rwSpinG : ElemG GF RwSpinF]

attribute [reducible, instance] RwSpinG.rwSpinG

def _root_.AeneasIris.RwLockAPI.LockState.word : LockState → Int
  | .free => 0
  | .read n => (n : Int) + 1
  | .write => -1

theorem _root_.AeneasIris.RwLockAPI.LockState.word_injective :
    Function.Injective LockState.word := by
  intro a b h
  cases a <;> cases b <;> simp_all [AeneasIris.RwLockAPI.LockState.word] <;> omega

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
variable [Aeneas.Std.ConcE.{1} -< E]
variable {T : Type} [Nonempty T]

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
  | .free, v => iprop(iOwn (F := RwSpinF) γ (● (ULift.up none : RwRes)) ∗ c ↦ v)
  | .read n, v => iprop(
      ∃ qout qrest : Qp, ⌜qout + qrest = 1⌝ ∗
        iOwn (F := RwSpinF) γ (● (ULift.up (some (RwPos.ofSucc n, RwPos.ofQp qout)) : RwRes)) ∗
        pointsTo c (DFrac.own qrest) v)
  | .write, _ => iprop(iOwn (F := RwSpinF) γ (● (ULift.up none : RwRes)))

def isRwLock (γ : GName) (lk : Handle T) (s : LockState) (v : T) : IProp GF :=
  iprop(lk.state ↦ s.word ∗ rwCore γ lk.data s v)

/-- `&mut T` is exactly the contents cell. -/
def writeGuard (_γ : GName) (lk : Handle T) (v : T) : IProp GF :=
  iprop(lk.data ↦ v)

/-- `&T` at client-visible strength `q`, backed by some share `s` of the cell. -/
def readGuardFrac (γ : GName) (lk : Handle T) (q : Qp) (v : T) : IProp GF :=
  iprop(∃ s : Qp,
    iOwn (F := RwSpinF) γ (◯ (ULift.up (some (RwPos.ofQp q, RwPos.ofQp s)) : RwRes)) ∗
    pointsTo lk.data (DFrac.own s) v)

instance (γ : GName) (lk : Handle T) (v : T) :
    Timeless (PROP := IProp GF) (writeGuard γ lk v) := by
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

instance readGuardFrac_timeless (γ : GName) (lk : Handle T) (q : Qp) (v : T) :
    Timeless (PROP := IProp GF) (readGuardFrac γ lk q v) := by
  unfold readGuardFrac
  refine @BI.exists_timeless _ _ _ _ ?_
  intro sq
  infer_instance

theorem readGuardFrac_split (γ : GName) (lk : Handle T) (q₁ q₂ : Qp) (v : T) :
    readGuardFrac (GF := GF) γ lk (q₁ + q₂) v
      ⊣⊢ iprop(readGuardFrac γ lk q₁ v ∗ readGuardFrac γ lk q₂ v) := by
  sorry

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
theorem readGuardFrac_state (γ : GName) (lk : Handle T) (s : LockState) (q : Qp) (v v' : T) :
    iprop(isRwLock γ lk s v ∗ readGuardFrac γ lk q v') ⊢@{IProp GF} iprop(⌜∃ n, s = .read n⌝) := by
  rcases s with _ | n | _
  all_goals (iintro ⟨H1, H2⟩;
             simp only [isRwLock, readGuardFrac, rwCore] at *)
  ·
    icases H1 with ⟨_, _, Hd1⟩
    icases H2 with ⟨%sq, _, Hd2⟩
    simp only [pointsToC] at *
    ihave %hne := ghost_map_elem_ne _ _ _ _ _ _ $$ Hd1 Hd2
    exact absurd rfl hne
  · ipureintro; exact ⟨n, rfl⟩
  ·
    icases H1 with ⟨_, Hown1⟩
    icases H2 with ⟨%sq, Hown2, _⟩
    ihave Hboth : iprop(iOwn (F := RwSpinF) γ _ ∗ iOwn (F := RwSpinF) γ _) $$ [Hown1 Hown2]
    · isplitl [Hown1]
      · iexact Hown1
      · iexact Hown2
    ihave %hv := iOwn_cmraValid_op $$ Hboth
    exfalso
    obtain ⟨⟨z⟩, hz⟩ := (Auth.auth_both_valid.mp hv).1 0
    cases z <;> simp_all [CMRA.op]

/-- ... and agrees with it on the contents. -/
theorem readGuardFrac_agree (γ : GName) (lk : Handle T) (s : LockState) (q : Qp) (v v' : T) :
    iprop(isRwLock γ lk s v ∗ readGuardFrac γ lk q v') ⊢@{IProp GF} iprop(⌜v = v'⌝) := by
  rcases s with _ | n | _
  all_goals (iintro ⟨H1, H2⟩;
             simp only [isRwLock, readGuardFrac, rwCore] at *)
  · icases H1 with ⟨_, _, Hd1⟩
    icases H2 with ⟨%sq, _, Hd2⟩
    ihave Hboth : iprop(pointsToC lk.data _ _ _ ∗ pointsToC lk.data _ _ _) $$ [Hd1 Hd2]
    · isplitl [Hd1]
      · iexact Hd1
      · iexact Hd2
    ihave %heq := pointsToC_agree lk.data _ _ _ _ _ _ $$ Hboth
    ipureintro
    exact Val.eq_of_Is (congrArg Prod.snd heq)
  · icases H1 with ⟨_, %qo, %qr, _, _, Hd1⟩
    icases H2 with ⟨%sq, _, Hd2⟩
    ihave Hboth : iprop(pointsToC lk.data _ _ _ ∗ pointsToC lk.data _ _ _) $$ [Hd1 Hd2]
    · isplitl [Hd1]
      · iexact Hd1
      · iexact Hd2
    ihave %heq := pointsToC_agree lk.data _ _ _ _ _ _ $$ Hboth
    ipureintro
    exact Val.eq_of_Is (congrArg Prod.snd heq)
  ·
    icases H1 with ⟨_, Hown1⟩
    icases H2 with ⟨%sq, Hown2, _⟩
    ihave Hboth : iprop(iOwn (F := RwSpinF) γ _ ∗ iOwn (F := RwSpinF) γ _) $$ [Hown1 Hown2]
    · isplitl [Hown1]
      · iexact Hown1
      · iexact Hown2
    ihave %hv := iOwn_cmraValid_op $$ Hboth
    exfalso
    have hincl := (Auth.auth_both_valid.mp hv).1 0
    obtain ⟨⟨z⟩, hz⟩ := hincl
    cases z <;> simp_all [CMRA.op]

/-- A write guard pins the lock to the write state. -/
theorem writeGuard_state (γ : GName) (lk : Handle T) (s : LockState) (v v' : T) :
    iprop(isRwLock γ lk s v ∗ writeGuard γ lk v') ⊢@{IProp GF} iprop(⌜s = .write⌝) := by
  iintro ⟨H1, H2⟩
  simp only [isRwLock, writeGuard] at *
  icases H1 with ⟨_, Hc⟩
  rcases s with _ | n | _
  ·
    simp only [rwCore, pointsToC] at *
    icases Hc with ⟨_, Hd⟩
    ihave %hne := ghost_map_elem_ne _ _ _ _ _ _ $$ H2 Hd
    exact absurd rfl hne
  ·
    simp only [rwCore, pointsToC] at *
    icases Hc with ⟨%qo, %qr, _, _, Hd⟩
    ihave %hne := ghost_map_elem_ne _ _ _ _ _ _ $$ H2 Hd
    exact absurd rfl hne
  · ipureintro; rfl

end Assertions


open Iris BI Aeneas.Data.Coinductive
open AeneasIris AeneasIris.Heap AeneasIris.HeapAPI
open Aeneas.Std (StateE StepE Loc RustHeap RustEffect Result)
open scoped Aeneas.Std
open AeneasIris.RwLockAPI
open AeneasIris.AtomicWpi
open AeneasIris.Step (stepH)
open AeneasIris.Conc (ConcH)

section

variable {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF] [HeapGS.{0} GF] [RwSpinG GF]
variable {E : Effect.{1}} [StateE RustHeap.{0} -< E] [StepE.{1} -< E]
variable [Aeneas.Std.ConcE.{1} -< E]
variable {Hd : Handler E GF} [stateH heapInterp -<ₕ Hd]
variable {m : Mode} [stepH GF m -<ₕ Hd]

variable [ConcH GF -<ₕ Hd]
variable {T : Type} [Nonempty T]

/-! ## Allocation -/

/-- **`new`.** Mirrors `new_spec`: the lock starts free, holding `v`. -/
theorem new_spec (v : T) (M : CoPset) :
    ⦃ emp ⦄ (new (E := E) v) @ Hd ; m ; M
    ⦃ lk, ∃ γ, isRwLock γ lk .free v ⦄ := by
  sorry

/-! ## Write -/

omit [Nonempty T] in
theorem try_write_spec (γ : GName) (lk : Handle T) :
    ⊢ ⟪ ∀ s v, isRwLock γ lk s v ⟫ Hd m (try_write (E := E) lk) @ (∅ : CoPset)
        ⟪ isRwLock γ lk (if s = .free then .write else s) v
        | rel, RET (if s = .free then some (mkWriteGuard lk, rel) else none)
        ; if s = .free then
            writeGuard γ lk v ∗
            □ (∀ v₁ : T, writeGuard γ lk v₁ -∗
                 ⟪ ∀ v₀, isRwLock γ lk .write v₀ ⟫
                     Hd m (rel (mkWriteGuard lk)) @ (∅ : CoPset)
                   ⟪ isRwLock γ lk .free v₁ | RET () ⟫)
          else emp ⟫ := by
  sorry


/-- **`write`.** Mirrors `write_spec`. -/
theorem write_spec (γ : GName) (lk : Handle T) :
    ⊢ ⟪ ∀ s v, isRwLock γ lk s v ⟫ Hd m (write (E := E) lk) @ (∅ : CoPset)
        ⟪ isRwLock γ lk .write v ∗ ⌜s = .free⌝
        | rel, RET (mkWriteGuard lk, rel)
        ; writeGuard γ lk v ∗
          □ (∀ v₁ : T, writeGuard γ lk v₁ -∗
               ⟪ ∀ v₀, isRwLock γ lk .write v₀ ⟫ Hd m (rel (mkWriteGuard lk)) @ (∅ : CoPset)
                   ⟪ isRwLock γ lk .free v₁ | RET () ⟫) ⟫ := by
  sorry

/-- **`write_release`.** -/
theorem write_release_spec (γ : GName) (g : WriteGuard T) (v₁ : T) :
    ⊢ writeGuard γ g.lock v₁ -∗
      ⟪ ∀ v₀, isRwLock γ g.lock .write v₀ ⟫
        Hd m (write_release (E := E) g) @ (∅ : CoPset)
      ⟪ isRwLock γ g.lock .free v₁ | RET () ⟫ := by
  sorry

/-! ## Read -/

/-- **`try_read`.** Mirrors `try_read_spec`. -/
theorem try_read_spec (γ : GName) (lk : Handle T) :
    ⊢ ⟪ ∀ s v, isRwLock γ lk s v ⟫ Hd m (try_read (E := E) lk) @ (∅ : CoPset)
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
                   | RET () ⟫) ⟫ := by
  sorry

theorem read_spec (γ : GName) (lk : Handle T) :
    ⊢ ⟪ ∀ s v, isRwLock γ lk s v ⟫ Hd m (read (E := E) lk) @ (∅ : CoPset)
        ⟪ (isRwLock γ lk (.read 0) v ∗ ⌜s = .free⌝) ∨
          (∃ k : Nat, isRwLock γ lk (.read (k + 1)) v ∗ ⌜s = .read k⌝)
        | rel, RET (mkReadGuard lk, rel)
        ; readGuardFrac γ lk 1 v ∗
          □ (readGuardFrac γ lk 1 v -∗
               ⟪ ∀ s', isRwLock γ lk s' v ⟫ Hd m (rel (mkReadGuard lk)) @ (∅ : CoPset)
                   ⟪ (isRwLock γ lk .free v ∗ ⌜s' = .read 0⌝) ∨
                     (∃ n : Nat, isRwLock γ lk (.read n) v ∗ ⌜s' = .read (n + 1)⌝)
                   | RET () ⟫) ⟫ := by
  sorry

/-- **`read_release`.** The counterpart of `write_release`, for the same reason. -/
theorem read_release_spec (γ : GName) (g : ReadGuard T) (v : T) :
    ⊢ readGuardFrac γ g.lock 1 v -∗
      ⟪ ∀ s, isRwLock γ g.lock s v ⟫
        Hd m (read_release (E := E) g) @ (∅ : CoPset)
      ⟪ (isRwLock γ g.lock .free v ∗ ⌜s = .read 0⌝) ∨
        (∃ n : Nat, isRwLock γ g.lock (.read n) v ∗ ⌜s = .read (n + 1)⌝)
      | RET () ⟫ := by
  sorry

/-! ## Dereference -/

/-- **`write_deref`.** -/
theorem write_deref_spec (γ : GName) (g : WriteGuard T) (v : T) (M : CoPset) :
    ⦃ writeGuard γ g.lock v ⦄ (write_deref (E := E) g) @ Hd ; m ; M
    ⦃ r, ⌜r = v⌝ ∗ writeGuard γ g.lock v ⦄ := by
  sorry

/-- **`read_deref`.** -/
theorem read_deref_spec (γ : GName) (g : ReadGuard T) (q : Qp) (v : T) (M : CoPset) :
    ⦃ readGuardFrac γ g.lock q v ⦄ (read_deref (E := E) g) @ Hd ; m ; M
    ⦃ r, ⌜r = v⌝ ∗ readGuardFrac γ g.lock q v ⦄ := by
  sorry

/-- **`write_deref_mut`.** Mirrors `write_deref_mut_spec`. -/
theorem write_deref_mut_spec (γ : GName) (g : WriteGuard T) (v : T) (M : CoPset) :
    ⦃ writeGuard γ g.lock v ⦄ (write_deref_mut (E := E) g) @ Hd ; m ; M
    ⦃ r, ∃ set back, ⌜r = (v, set, back)⌝ ∗
        writeGuard γ g.lock v ∗
        □ (∀ v₀ : T, ∀ v' : T, writeGuard γ g.lock v₀ -∗
             wpi_mask GF Hd m (set v')
               (fun g' => iprop(⌜g' = g⌝ ∗ writeGuard γ g.lock v')) ⊤) ⦄ := by
  sorry

theorem drop_spec (γ : GName) (lk : Handle T) (v : T) (M : CoPset) :
    ⦃ isRwLock γ lk .free v ⦄ (drop (E := E) lk) @ Hd ; m ; M
    ⦃ r, ⌜r = ()⌝ ⦄ := by
  sorry

/-! ## The instance

Every field is one of the definitions or theorems above; nothing is proved here.
-/

noncomputable instance instRwLockAPI :
    RwLockAPI GF Hd m T (Handle T) (ReadGuard T) (WriteGuard T) where
  new := new
  drop := drop
  try_read := try_read
  try_write := try_write
  read := read
  write := write
  read_deref := read_deref
  write_deref := write_deref
  write_deref_mut := write_deref_mut

  readLock g := g.lock
  writeLock g := g.lock
  mkReadGuard := mkReadGuard
  mkWriteGuard := mkWriteGuard
  readLock_mk _ := rfl
  writeLock_mk _ := rfl

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
