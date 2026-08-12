import AeneasIris.HeapAPI
import Iris.Instances.Lib.LaterCredits
import Iris.Algebra.Auth
import Iris.Algebra.Agree

namespace AeneasIris.Arc

open Iris BI Aeneas.Data.Coinductive
open AeneasIris AeneasIris.Heap AeneasIris.HeapAPI
open Aeneas.Std (StateE StepE Loc Val RustHeap)
open scoped Aeneas.Std
open AeneasIris.Step (lat LaterModality stepH)

/-- Model of `my_std::Arc<T>`.

The payload is a *cell*, not a field. `Arc<T>` is a shared pointer: every clone
must observe the same `T`, so storing it by value would give each clone its own
copy and lose the only property the type exists for -- `Arc<RwLock<Node>>` would
hand out unrelated locks. -/
structure Handle (T : Type) where
  strong : Loc
  weak : Loc
  data : Loc
deriving DecidableEq, Repr

inductive WeakHandle (T : Type)
  | dangling
  | live (h : Handle T)
deriving DecidableEq

section Code

variable {E : Effect.{1}} [StateE RustHeap.{0} -< E] [StepE.{1} -< E]
variable {T : Type} [Nonempty T]

noncomputable def new (x : T) : ITree E (Handle T) := do
  let s ← alloc (1 : Int)
  let w ← alloc (1 : Int)
  let d ← alloc x
  return ⟨s, w, d⟩

/-- `Deref for Arc`.

A heap read, not a projection -- which is what makes the sharing observable, and
what the generated signature `Arc T -> Result T` already says. -/
noncomputable def deref (a : Handle T) : ITree E T :=
  load a.data

/-- `Arc::strong_count`. -/
noncomputable def strong_count (a : Handle T) : ITree E Int :=
  load a.strong

noncomputable def clone (a : Handle T) : ITree E (Handle T) := do
  let _ ← faa a.strong (1 : Int)
  return a

noncomputable def downgrade (a : Handle T) : ITree E (WeakHandle T) := do
  let _ ← faa a.weak (1 : Int)
  return .live a

/-- Releasing one strong reference. The payload is freed by the last one to
leave; the two counter cells outlive it and go when the last weak does. -/
noncomputable def dropStrong (a : Handle T) : ITree E Bool := do
  let old : Int ← faa a.strong (-1)
  if old = 1 then
    let _ ← HeapAPI.free a.data
    return true
  else
    return false

def weakNew : WeakHandle T := .dangling

noncomputable def weakClone (w : WeakHandle T) : ITree E (WeakHandle T) :=
  match w with
  | .dangling => ITree.ret .dangling
  | .live a => do
      let _ ← faa a.weak (1 : Int)
      return .live a

noncomputable def weakDrop (w : WeakHandle T) : ITree E Unit :=
  match w with
  | .dangling => ITree.ret ()
  | .live a => do
      let old : Int ← faa a.weak (-1)
      if old = 1 then
        let _ ← HeapAPI.free a.strong
        HeapAPI.free a.weak
      else
        return ()

/-! No `yield` here: this is a CAS retry, not a wait.

The loop exits as soon as no other thread interferes with the count, so running
on is what makes it finish — unlike `RwLock.read_acquire`, which cannot exit
until another thread releases the lock and therefore must yield. Upgrading also
fails outright (`.inr none`) once the strong count hits zero, so there is
nothing to wait *for*. -/

noncomputable def tryUpgrade (a : Handle T) : ITree E (Option (Handle T)) :=
  ITree.iter (fun _ => do
    let n : Int ← load a.strong
    if n = 0 then
      return .inr none
    else
      let ok ← cas a.strong n (n + 1)
      if ok then return .inr (some a) else return .inl ()) ()

noncomputable def weakUpgrade (w : WeakHandle T) : ITree E (Option (Handle T)) :=
  match w with
  | .dangling => ITree.ret none
  | .live a => tryUpgrade a

noncomputable def weakStrongCount (w : WeakHandle T) : ITree E Int :=
  match w with
  | .dangling => ITree.ret 0
  | .live a => load a.strong

end Code

section Assertions

variable {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF] [G : HeapGS.{0} GF]
variable {T : Type}

def physical (a : Handle T) : Nat → Nat → IProp GF
  | 0, 0 => iprop(emp)
  | 0, (m + 1) => iprop(a.strong ↦ (0 : Int) ∗ a.weak ↦ ((m : Int) + 1))
  | (n + 1), m => iprop(a.strong ↦ ((n : Int) + 1) ∗ a.weak ↦ ((m : Int) + 1))

def isDanglingWeak (w : WeakHandle T) : Prop := w = .dangling

/-! ## Ghost state

Every piece here is stock Iris. `Option (Agree ·)` pins which allocation and
which payload a ghost name is talking about, so two handles carrying the same
`γ` cannot disagree. The two `Credit`s (`= Nat`, from `LaterCredits`) are the
strong and weak counts: a `Nat` has a unit, which is what lets a single handle
be a fragment holding `(1, 0)` or `(0, 1)` and nothing else.

The `ULift` is for universes only -- `iOwn` wants `OFunctorPre.{1,1,1}` and the
payload lives in `Type 0`. `RwSpinF` does the same. -/

abbrev ArcMeta (T : Type) := LeibnizO (Handle T × T)
abbrev ArcRes (T : Type) := ULift.{1} (Option (Agree (ArcMeta T)) × (Credit × Credit))
abbrev ArcF (T : Type) : COFE.OFunctorPre.{1,1,1} := Auth.AuthURF (constOF (ArcRes T))

class ArcG (GF : BundledGFunctors) (T : Type) where
  [arcG : ElemG GF (ArcF T)]

attribute [reducible, instance] ArcG.arcG

section Ghost
variable [ArcG GF T]

/-- A resource: optional agreement on the allocation, plus credits.

Agreement and credits are separated in the *fragments* below because they behave
differently -- the agreement is duplicable, a credit is not. -/
def res (md : Option (Handle T × T)) (n m : Nat) : ArcRes T :=
  ULift.up (md.map (fun x => toAgree (LeibnizO.mk x)), (n, m))

/-- The authority: the physical control block, the payload while anyone still
holds it, and the counts.

`a` and `v` are existential because no client statement names them -- which
allocation backs a ghost name is the library's business, and the agreement in
the metadata is what stops two handles from disagreeing about it. -/
def arcAuth (γ : GName) (n m : Nat) : IProp GF := iprop(
  ∃ a : Handle T, ∃ v : T,
    physical a n m ∗
    (match n with | 0 => iprop(emp) | _ + 1 => iprop(a.data ↦ v)) ∗
    iOwn (F := ArcF T) γ (● res (some (a, v)) n m))

/-- Agreement on which allocation and payload a ghost name denotes. Carries no
credit, so it is duplicable. -/
def arcMetaOwn (γ : GName) (a : Handle T) (v : T) : IProp GF :=
  iprop(iOwn (F := ArcF T) γ (◯ res (some (a, v)) 0 0))

/-- One strong credit, and nothing else. -/
def arcStrongOwn (γ : GName) : IProp GF :=
  iprop(iOwn (F := ArcF T) γ (◯ res (T := T) none 1 0))

/-- One weak credit. -/
def arcWeakOwn (γ : GName) : IProp GF :=
  iprop(iOwn (F := ArcF T) γ (◯ res (T := T) none 0 1))

/-- One strong reference. -/
def isArc (γ : GName) (a : Handle T) (v : T) : IProp GF :=
  iprop(arcMetaOwn γ a v ∗ arcStrongOwn (T := T) γ)

/-- One weak reference. -/
def isWeak (γ : GName) (a : Handle T) (v : T) : IProp GF :=
  iprop(arcMetaOwn γ a v ∗ arcWeakOwn (T := T) γ)

end Ghost

instance (a : Handle T) (n m : Nat) : Timeless (PROP := IProp GF) (physical a n m) := by
  cases n <;> cases m <;> (unfold physical; infer_instance)

end Assertions

end AeneasIris.Arc
