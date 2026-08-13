import AeneasIris.HeapAPI
import AeneasIris.Conc
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

/-- The resource: an outstanding reader credit and the share it holds.

Lifted to `Type 1` because ghost state in this development sits one universe
above its carriers (`iOwn` expects `OFunctorPre.{1,1,1}`). -/
abbrev RwRes := ULift.{1} (Option (RwPos × RwPos))
abbrev RwSpinF : COFE.OFunctorPre.{1,1,1} := Auth.AuthURF (constOF RwRes)

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
variable [Aeneas.Std.ConcE.{1} -< E]
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

/-! ## Acquisition and release: the synchronisation points

Each of the four is wrapped in `sync`, so each begins with a yield. That is what
makes every critical section bracketed by scheduling points — without it an
uncontended acquire-modify-release performs no yield at all, and since a yield
is the only place control passes to another thread, one thread could run
through unboundedly many critical sections while no other is ever scheduled.

`waitUntil` supplies the *other* yield, on the branch where an attempt fails:
that loop can only exit because another thread releases the lock, so without it
the spin is a livelock.

Neither yield stops an invariant being opened at the linearisation point — the
successful CAS inside `try_read`/`try_write`, a single event with no yield near
it. `wpi_bind` and every heap rule are mask-polymorphic; only `yield` demands
`⊤`. What is ruled out is holding an invariant open *across* an acquire, which
is the deadlock-prone pattern. -/

noncomputable def read_acquire (lk : Handle T) : ITree E (ReadGuard T) :=
  AeneasIris.ConcE.sync (AeneasIris.ConcE.waitUntil (try_read (E := E) lk))

noncomputable def write_acquire (lk : Handle T) : ITree E (WriteGuard T) :=
  AeneasIris.ConcE.sync (AeneasIris.ConcE.waitUntil (try_write (E := E) lk))

/-! Release does *not* yield, and the difference is not a matter of taste.

This loop retries a failed CAS. It exits as soon as no other thread interferes,
so running on without yielding is what makes it finish — a `yield` here would
only hand control away at the one moment progress is available. Contrast
`read_acquire`, whose loop cannot exit until another thread acts.

The rule: **yield where the loop waits for someone else, not where it retries
its own work.** -/

noncomputable def read_release (g : ReadGuard T) : ITree E Unit :=
  AeneasIris.ConcE.sync <| ITree.iter (fun _ => do
    let n : Int ← load g.lock.state
    let ok ← cas g.lock.state n (n - 1)
    if ok then return .inr () else return .inl ()) ()

noncomputable def write_release (g : WriteGuard T) : ITree E Unit :=
  AeneasIris.ConcE.sync (store g.lock.state (0 : Int))

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

variable {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF] [G : HeapGS.{0} GF] [RwSpinG GF]
variable {T : Type}

/-- The lock's own view of the contents cell, as a function of the abstract state.

Ported from the HeapLang development (`SpinRwLock.lean`, `rwCore`). The point is
that data ownership is **state-dependent**: it is the lock that holds the cell
when nobody has it, a *residual* share while readers are out, and nothing at all
while a writer holds it. The previous definition here kept the full cell in every
state, which made `isRwLock .write v ∗ writeGuard v` demand `data ↦ v ∗ data ↦ v`
-- that is, `False` -- so no guard-producing spec could be stated. -/
def rwCore (γ : GName) (c : Loc) : LockState → T → IProp GF
  | .free, v => iprop(iOwn (F := RwSpinF) γ (● (ULift.up none : RwRes)) ∗ c ↦ v)
  | .read n, v => iprop(
      ∃ qout qrest : Qp, ⌜qout + qrest = 1⌝ ∗
        iOwn (F := RwSpinF) γ (● (ULift.up (some (RwPos.ofSucc n, RwPos.ofQp qout)) : RwRes)) ∗
        pointsTo c (DFrac.own qrest) v)
  | .write, _ => iprop(iOwn (F := RwSpinF) γ (● (ULift.up none : RwRes)))

def isRwLock (γ : GName) (lk : Handle T) (s : LockState) (v : T) : IProp GF :=
  iprop(lk.state ↦ s.word ∗ rwCore γ lk.data s v)

/-- `&mut T` is exactly the contents cell. No ghost token is needed: owning the
cell in full is already unforgeable and already excludes every other guard. -/
def writeGuard (_γ : GName) (lk : Handle T) (v : T) : IProp GF :=
  iprop(lk.data ↦ v)

/-- `&T` at client-visible strength `q`, backed by some share `s` of the cell.
`s` is existential because no client statement mentions it -- how much of the
cell a permit is worth is the library's business. -/
def readGuardFrac (γ : GName) (lk : Handle T) (q : Qp) (v : T) : IProp GF :=
  iprop(∃ s : Qp,
    iOwn (F := RwSpinF) γ (◯ (ULift.up (some (RwPos.ofQp q, RwPos.ofQp s)) : RwRes)) ∗
    pointsTo lk.data (DFrac.own s) v)

instance (γ : GName) (lk : Handle T) (v : T) :
    Timeless (PROP := IProp GF) (writeGuard γ lk v) := by
  unfold writeGuard; infer_instance

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
  /- Both hold the counter cell outright, whatever the state. `pointsToC` has to
  be unfolded by hand: `ispecialize` does not see through a `def`. -/
  simp only [pointsToC] at *
  ihave %hne := ghost_map_elem_ne _ _ _ _ _ _ $$ Hst1 Hst2
  exact absurd rfl hne

/-- A read permit pins the lock to a read state. -/
theorem readGuardFrac_state (γ : GName) (lk : Handle T) (s : LockState) (q : Qp) (v v' : T) :
    iprop(isRwLock γ lk s v ∗ readGuardFrac γ lk q v') ⊢@{IProp GF} iprop(⌜∃ n, s = .read n⌝) := by
  rcases s with _ | n | _
  all_goals (iintro ⟨H1, H2⟩;
             simp only [isRwLock, readGuardFrac, rwCore] at *)
  · /- free: the core owns the whole cell, the permit a share of it. -/
    icases H1 with ⟨_, _, Hd1⟩
    icases H2 with ⟨%sq, _, Hd2⟩
    simp only [pointsToC] at *
    ihave %hne := ghost_map_elem_ne _ _ _ _ _ _ $$ Hd1 Hd2
    exact absurd rfl hne
  · ipureintro; exact ⟨n, rfl⟩
  · /- write: `● none` cannot contain the permit's `◯ (some _)`. -/
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
  /- Split on the state *before* unfolding: `simp only … at H` cannot reach a
  proof-mode hypothesis, so the `match` in `rwCore` has to be reduced by the
  case split itself. -/
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
  · /- write: the core holds no cell at all, so there is nothing to agree with.
    The contradiction is algebraic instead -- the write authority is `● none`,
    and a read permit carries `◯ (some _)`, which would have to be included in
    it. -/
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
  · /- free: the core still holds the whole cell, and so does the guard. -/
    simp only [rwCore, pointsToC] at *
    icases Hc with ⟨_, Hd⟩
    ihave %hne := ghost_map_elem_ne _ _ _ _ _ _ $$ H2 Hd
    exact absurd rfl hne
  · /- read n: the core holds a share, which still excludes a full one. -/
    simp only [rwCore, pointsToC] at *
    icases Hc with ⟨%qo, %qr, _, _, Hd⟩
    ihave %hne := ghost_map_elem_ne _ _ _ _ _ _ $$ H2 Hd
    exact absurd rfl hne
  · ipureintro; rfl

end Assertions

end AeneasIris.RwLock
