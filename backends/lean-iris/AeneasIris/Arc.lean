import AeneasIris.HeapAPI
import Iris.Instances.Lib.LaterCredits
import Iris.Algebra.Auth
import Iris.Algebra.Agree

namespace AeneasIris.Arc

open Iris BI Aeneas.Data.Coinductive
open AeneasIris AeneasIris.Heap AeneasIris.HeapAPI
open Aeneas.Std (StateE StepE Loc Val RustHeap)
open scoped Aeneas.Std
open AeneasIris.Step (lat stepH)

/-- Model of `my_std::Arc<T>`. -/
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

/-- `Deref for Arc`. -/
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

/-- Releasing one strong reference. -/
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

/-! No `yield` here: this is a CAS retry, not a wait. -/

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

/-! ## Ghost state -/

abbrev ArcMeta (T : Type) := LeibnizO (Handle T × T)
abbrev ArcRes (T : Type) := ULift.{1} (Option (Agree (ArcMeta T)) × (Credit × Credit))
abbrev ArcF (T : Type) : COFE.OFunctorPre.{1,1,1} := Auth.AuthURF (constOF (ArcRes T))

class ArcG (GF : BundledGFunctors) (T : Type) where
  [arcG : ElemG GF (ArcF T)]

attribute [reducible, instance] ArcG.arcG

section Ghost
variable [ArcG GF T]

/-- A resource: optional agreement on the allocation, plus credits. -/
def res (md : Option (Handle T × T)) (n m : Nat) : ArcRes T :=
  ULift.up (md.map (fun x => toAgree (LeibnizO.mk x)), (n, m))

/-- The authority: the physical control block, the payload while anyone still holds it, and the counts. -/
def arcAuth (γ : GName) (n m : Nat) : IProp GF := iprop(
  ∃ a : Handle T, ∃ v : T,
    physical a n m ∗
    (match n with
     | 0 => iprop(emp)
     | _ + 1 => iprop(∃ qrest : Qp, pointsTo a.data (DFrac.own qrest) v)) ∗
    iOwn (F := ArcF T) γ (● res (some (a, v)) n m))

/-- Agreement on which allocation and payload a ghost name denotes. -/
def arcMetaOwn (γ : GName) (a : Handle T) (v : T) : IProp GF :=
  iprop(iOwn (F := ArcF T) γ (◯ res (some (a, v)) 0 0))

/-- One strong credit, and nothing else. -/
def arcStrongOwn (γ : GName) : IProp GF :=
  iprop(iOwn (F := ArcF T) γ (◯ res (T := T) none 1 0))

/-- One weak credit. -/
def arcWeakOwn (γ : GName) : IProp GF :=
  iprop(iOwn (F := ArcF T) γ (◯ res (T := T) none 0 1))

/-- One strong reference: agreement, a strong credit, and a share of the payload cell. -/
def isArc (γ : GName) (a : Handle T) (v : T) : IProp GF :=
  iprop(∃ q : Qp, arcMetaOwn γ a v ∗ arcStrongOwn (T := T) γ ∗
    pointsTo a.data (DFrac.own q) v)

/-- One weak reference. -/
def isWeak (γ : GName) (a : Handle T) (v : T) : IProp GF :=
  iprop(arcMetaOwn γ a v ∗ arcWeakOwn (T := T) γ)

/-! ### Resource algebra facts

`res` is componentwise: the metadata slot is an `Agree`, so two fragments that
disagree are already invalid, and the two counters are `Credit = Nat` under
addition with `0` as unit.  Everything below is read off from those two facts
via `Auth.auth_both_valid`, exactly as the lock does. -/

@[simp] theorem res_op (md : Option (Handle T × T)) (n m n' m' : Nat) :
    res md n m • res (T := T) none n' m' = res md (n + n') (m + m') := by
  cases md <;> rfl

/-- Splitting a credit off the fragment. -/
theorem res_split (n m n' m' : Nat) :
    res (T := T) none (n + n') (m + m') = res (T := T) none n m • res (T := T) none n' m' := rfl

/-- The metadata fragment is duplicable: `Agree` is core-id and the two credits
are the unit.  Given explicitly -- synthesis times out looking for it through
`ULift`, `Option`, `Agree` and the pair. -/
instance arcMeta_coreId (a : Handle T) (v : T) :
    CMRA.CoreId (res (T := T) (some (a, v)) 0 0) := ⟨.rfl⟩

/-- Hence `arcMetaOwn` is persistent. -/
instance arcMetaOwn_persistent (γ : GName) (a : Handle T) (v : T) :
    Persistent (arcMetaOwn (GF := GF) γ a v) := by
  unfold arcMetaOwn
  infer_instance

/-- Holding a strong credit forces the authority's strong count to be positive.
This is what lets `clone`/`drop` know they are not acting on a dead `Arc`, and
it travels with the *linear* credit rather than with any persistent assertion. -/
theorem arcAuth_strong_pos (γ : GName) (md : Option (Handle T × T)) (n m : Nat) :
    iprop(iOwn (F := ArcF T) γ (● res md n m) ∗ arcStrongOwn (T := T) γ)
      ⊢@{IProp GF} iprop(⌜1 ≤ n⌝) := by
  iintro ⟨H1, H2⟩
  simp only [arcStrongOwn] at *
  ihave Hboth : iprop(iOwn (F := ArcF T) γ _ ∗ iOwn (F := ArcF T) γ _) $$ [H1 H2]
  · isplitl [H1]
    · iexact H1
    · iexact H2
  ihave %hv := iOwn_cmraValid_op $$ Hboth
  ipureintro
  obtain ⟨⟨⟨zmd, zn, zm⟩⟩, hz⟩ := (Auth.auth_both_valid.mp hv).1 0
  simp only [res, CMRA.op, Prod.op] at hz
  obtain ⟨-, hn, -⟩ := hz
  /- `Credit` is discrete, so its `≡{0}≡` is definitionally `Eq`. -/
  have hn' : n = 1 + zn := hn
  grind

/-- The metadata fragment pins down which allocation and payload the ghost name
denotes.  `arcMetaOwn` is persistent, so this is available to every holder. -/
theorem arcAuth_meta_agree (γ : GName) (a a' : Handle T) (v v' : T) (n m : Nat) :
    iprop(iOwn (F := ArcF T) γ (● res (some (a', v')) n m) ∗ arcMetaOwn γ a v)
      ⊢@{IProp GF} iprop(⌜a' = a ∧ v' = v⌝) := by
  iintro ⟨H1, H2⟩
  simp only [arcMetaOwn] at *
  ihave Hboth : iprop(iOwn (F := ArcF T) γ _ ∗ iOwn (F := ArcF T) γ _) $$ [H1 H2]
  · isplitl [H1]
    · iexact H1
    · iexact H2
  ihave %hv := iOwn_cmraValid_op $$ Hboth
  ipureintro
  obtain ⟨hincl, hvalid⟩ := Auth.auth_both_valid.mp hv
  obtain ⟨⟨⟨zmd, zn, zm⟩⟩, hz⟩ := hincl 0
  simp only [res, CMRA.op, Prod.op] at hz
  obtain ⟨hmd, -, -⟩ := hz
  dsimp only at hmd
  /- The metadata slot is an `Agree`, so the fragment's entry is included in the
  authority's, and inclusion between `toAgree`s is equality of the carriers. -/
  have heq : (LeibnizO.mk (a, v) : ArcMeta T) ≡{0}≡ LeibnizO.mk (a', v') := by
    cases zmd with
    | none =>
      have h : (toAgree (LeibnizO.mk (a', v')) : Agree (ArcMeta T))
          ≡{0}≡ toAgree (LeibnizO.mk (a, v)) := hmd
      exact (Agree.toAgree_injN h).symm
    | some w =>
      have h : (toAgree (LeibnizO.mk (a', v')) : Agree (ArcMeta T))
          ≡{0}≡ toAgree (LeibnizO.mk (a, v)) • w := hmd
      exact Agree.toAgree_includedN.mp ⟨w, h⟩
  have : (a, v) = (a', v') := LeibnizO.dist_inj heq
  grind

/-! Both facts above are pure, so they can be read off without giving up the
resources they were read from.  The `$$ [...]` form of `ihave` consumes what it
is handed, so the callers want these variants. -/

/-- A pure consequence can be taken without spending the hypothesis. -/
private theorem keep_pure {P : IProp GF} {φ : Prop} (h : P ⊢ iprop(⌜φ⌝)) :
    P ⊢ iprop(⌜φ⌝ ∗ P) :=
  (BI.and_intro h .rfl).trans BI.persistent_and_sep_mp

theorem arcAuth_strong_pos_keep (γ : GName) (md : Option (Handle T × T)) (n m : Nat) :
    iprop(iOwn (F := ArcF T) γ (● res md n m) ∗ arcStrongOwn (T := T) γ)
      ⊢@{IProp GF} iprop(⌜1 ≤ n⌝ ∗
        (iOwn (F := ArcF T) γ (● res md n m) ∗ arcStrongOwn (T := T) γ)) :=
  keep_pure (arcAuth_strong_pos γ md n m)

theorem arcAuth_meta_agree_keep (γ : GName) (a a' : Handle T) (v v' : T) (n m : Nat) :
    iprop(iOwn (F := ArcF T) γ (● res (some (a', v')) n m) ∗ arcMetaOwn γ a v)
      ⊢@{IProp GF} iprop(⌜a' = a ∧ v' = v⌝ ∗
        (iOwn (F := ArcF T) γ (● res (some (a', v')) n m) ∗ arcMetaOwn γ a v)) :=
  keep_pure (arcAuth_meta_agree γ a a' v v' n m)

end Ghost

instance (a : Handle T) (n m : Nat) : Timeless (PROP := IProp GF) (physical a n m) := by
  cases n <;> cases m <;> (unfold physical; infer_instance)

end Assertions

end AeneasIris.Arc
