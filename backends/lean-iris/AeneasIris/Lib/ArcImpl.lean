import AeneasIris.Lib.ArcAPI
import AeneasIris.Effects.HeapAPI
import Iris.Instances.Lib.LaterCredits
import Iris.Algebra.Auth
import Iris.Algebra.Agree
import AeneasIris.Tactics.Core
import Iris.BI.Lib.Atomic
import AeneasIris.AtomicWpi

/-! # The ITree `Arc`: the implementation, its specs, and the instance -/

unseal Aeneas.Std.Result

namespace AeneasIris.ArcImpl

open Iris BI Aeneas.Data.Coinductive
open AeneasIris AeneasIris.Heap AeneasIris.HeapAPI
open Aeneas.Std (StateE StepE Loc Val RustHeap)
open scoped Aeneas.Std
open AeneasIris.Step (lat stepH)
open Iris.CMRA Iris.OFE
open scoped Iris

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

noncomputable def deref (a : Handle T) : ITree E T :=
  load a.data

noncomputable def strong_count (a : Handle T) : ITree E Int :=
  load a.strong

noncomputable def clone (a : Handle T) : ITree E (Handle T) := do
  let _ ← faa a.strong (1 : Int)
  return a

noncomputable def downgrade (a : Handle T) : ITree E (WeakHandle T) := do
  let _ ← faa a.weak (1 : Int)
  return .live a

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

/-- No `yield`: this is a CAS retry, not a wait. -/
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

/-- The control block. At `0, 0` the whole allocation is gone, so there are no
cells left to own -- which is why every spec first has to rule that case out. -/
def physical (a : Handle T) : Nat → Nat → IProp GF
  | 0, 0 => iprop(emp)
  | 0, (w + 1) => iprop(a.strong ↦ (0 : Int) ∗ a.weak ↦ ((w : Int) + 1))
  | (n + 1), w => iprop(a.strong ↦ ((n : Int) + 1) ∗ a.weak ↦ ((w : Int) + 1))

abbrev ArcMeta (T : Type) := LeibnizO (Handle T × T)
abbrev ArcRes (T : Type) := ULift.{1} (Option (Agree (ArcMeta T)) × (Credit × Credit))
abbrev ArcF (T : Type) : COFE.OFunctorPre.{1,1,1} := Auth.AuthURF (constOF (ArcRes T))

class ArcG (GF : BundledGFunctors) (T : Type) where
  [arcG : ElemG GF (ArcF T)]

attribute [reducible, instance] ArcG.arcG

section Ghost
variable [ArcG GF T]

/-- Agreement on the allocation, plus one credit per reference of each kind. -/
def res (md : Option (Handle T × T)) (n w : Nat) : ArcRes T :=
  ULift.up (md.map (fun x => toAgree (LeibnizO.mk x)), (n, w))

def arcAuth (γ : GName) (n w : Nat) : IProp GF := iprop(
  ∃ a : Handle T, ∃ v : T,
    physical a n w ∗
    (match n with
     | 0 => iprop(emp)
     | _ + 1 => iprop(∃ qrest : Qp, pointsTo a.data (DFrac.own qrest) v)) ∗
    iOwn (F := ArcF T) γ (● res (some (a, v)) n w))

def arcMetaOwn (γ : GName) (a : Handle T) (v : T) : IProp GF :=
  iprop(iOwn (F := ArcF T) γ (◯ res (some (a, v)) 0 0))

def arcStrongOwn (γ : GName) : IProp GF :=
  iprop(iOwn (F := ArcF T) γ (◯ res (T := T) none 1 0))

def arcWeakOwn (γ : GName) : IProp GF :=
  iprop(iOwn (F := ArcF T) γ (◯ res (T := T) none 0 1))

/-- One strong reference: agreement, a strong credit, and a share of the payload
cell -- the share is what makes `deref` an ordinary read. -/
def isArc (γ : GName) (a : Handle T) (v : T) : IProp GF :=
  iprop(∃ q : Qp, arcMetaOwn γ a v ∗ arcStrongOwn (T := T) γ ∗
    pointsTo a.data (DFrac.own q) v)

def isWeak (γ : GName) (a : Handle T) (v : T) : IProp GF :=
  iprop(arcMetaOwn γ a v ∗ arcWeakOwn (T := T) γ)

@[simp] theorem res_op (md : Option (Handle T × T)) (n w n' w' : Nat) :
    res md n w • res (T := T) none n' w' = res md (n + n') (w + w') := by
  cases md <;> rfl

theorem res_split (n w n' w' : Nat) :
    res (T := T) none (n + n') (w + w') = res (T := T) none n w • res (T := T) none n' w' := rfl

/-- Given explicitly: synthesis times out looking for it through `ULift`,
`Option`, `Agree` and the pair. -/
instance arcMeta_coreId (a : Handle T) (v : T) :
    CMRA.CoreId (res (T := T) (some (a, v)) 0 0) := ⟨.rfl⟩

instance arcMetaOwn_persistent (γ : GName) (a : Handle T) (v : T) :
    Persistent (arcMetaOwn (GF := GF) γ a v) := by
  unfold arcMetaOwn
  infer_instance

/-- Holding a credit forces the matching count to be positive: `clone`/`drop`
learn they are not acting on a dead `Arc`, and they learn it from the *linear*
credit rather than from anything persistent. Read off, like the lock does, by
combining the two `iOwn`s and projecting `Auth.auth_both_valid`'s inclusion. -/
theorem arcAuth_strong_pos (γ : GName) (md : Option (Handle T × T)) (n w : Nat) :
    iprop(iOwn (F := ArcF T) γ (● res md n w) ∗ arcStrongOwn (T := T) γ)
      ⊢@{IProp GF} iprop(⌜1 ≤ n⌝) := by
  iintro ⟨H1, H2⟩
  simp only [arcStrongOwn] at *
  ihave Hboth : iprop(iOwn (F := ArcF T) γ _ ∗ iOwn (F := ArcF T) γ _) $$ [H1 H2]
  · isplitl [H1]
    · iexact H1
    · iexact H2
  ihave %hv := iOwn_cmraValid_op $$ Hboth
  ipureintro
  obtain ⟨⟨⟨zmd, zn, zw⟩⟩, hz⟩ := (Auth.auth_both_valid.mp hv).1 0
  simp only [res, CMRA.op, Prod.op] at hz
  obtain ⟨-, hn, -⟩ := hz
  have hn' : n = 1 + zn := hn
  grind

theorem arcAuth_weak_pos (γ : GName) (md : Option (Handle T × T)) (n w : Nat) :
    iprop(iOwn (F := ArcF T) γ (● res md n w) ∗ arcWeakOwn (T := T) γ)
      ⊢@{IProp GF} iprop(⌜1 ≤ w⌝) := by
  iintro ⟨H1, H2⟩
  simp only [arcWeakOwn] at *
  ihave Hboth : iprop(iOwn (F := ArcF T) γ _ ∗ iOwn (F := ArcF T) γ _) $$ [H1 H2]
  · isplitl [H1]
    · iexact H1
    · iexact H2
  ihave %hv := iOwn_cmraValid_op $$ Hboth
  ipureintro
  obtain ⟨⟨⟨zmd, zn, zw⟩⟩, hz⟩ := (Auth.auth_both_valid.mp hv).1 0
  simp only [res, CMRA.op, Prod.op] at hz
  obtain ⟨-, -, hw⟩ := hz
  have hw' : w = 1 + zw := hw
  grind

/-- The metadata fragment pins down which allocation and payload the ghost name
denotes: the slot is an `Agree`, so the fragment's entry is included in the
authority's, and inclusion between `toAgree`s is equality of the carriers. -/
theorem arcAuth_meta_agree (γ : GName) (a a' : Handle T) (v v' : T) (n w : Nat) :
    iprop(iOwn (F := ArcF T) γ (● res (some (a', v')) n w) ∗ arcMetaOwn γ a v)
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
  obtain ⟨⟨⟨zmd, zn, zw⟩⟩, hz⟩ := hincl 0
  simp only [res, CMRA.op, Prod.op] at hz
  obtain ⟨hmd, -, -⟩ := hz
  dsimp only at hmd
  have heq : (LeibnizO.mk (a, v) : ArcMeta T) ≡{0}≡ LeibnizO.mk (a', v') := by
    cases zmd with
    | none =>
      have h : (toAgree (LeibnizO.mk (a', v')) : Agree (ArcMeta T))
          ≡{0}≡ toAgree (LeibnizO.mk (a, v)) := hmd
      exact (Agree.toAgree_injN h).symm
    | some z =>
      have h : (toAgree (LeibnizO.mk (a', v')) : Agree (ArcMeta T))
          ≡{0}≡ toAgree (LeibnizO.mk (a, v)) • z := hmd
      exact Agree.toAgree_includedN.mp ⟨z, h⟩
  have : (a, v) = (a', v') := LeibnizO.dist_inj heq
  grind

/-- The facts above are pure, so they can be read off without giving up the
resources they came from. `ihave ... $$ [H₁ H₂]` hands its arguments over, and
every caller still needs the authority in order to commit it. -/
private theorem keep_pure {P : IProp GF} {φ : Prop} (h : P ⊢ iprop(⌜φ⌝)) :
    P ⊢ iprop(⌜φ⌝ ∗ P) :=
  (BI.and_intro h .rfl).trans BI.persistent_and_sep_mp

theorem arcAuth_strong_pos_keep (γ : GName) (md : Option (Handle T × T)) (n w : Nat) :
    iprop(iOwn (F := ArcF T) γ (● res md n w) ∗ arcStrongOwn (T := T) γ)
      ⊢@{IProp GF} iprop(⌜1 ≤ n⌝ ∗
        (iOwn (F := ArcF T) γ (● res md n w) ∗ arcStrongOwn (T := T) γ)) :=
  keep_pure (arcAuth_strong_pos γ md n w)

theorem arcAuth_meta_agree_keep (γ : GName) (a a' : Handle T) (v v' : T) (n w : Nat) :
    iprop(iOwn (F := ArcF T) γ (● res (some (a', v')) n w) ∗ arcMetaOwn γ a v)
      ⊢@{IProp GF} iprop(⌜a' = a ∧ v' = v⌝ ∗
        (iOwn (F := ArcF T) γ (● res (some (a', v')) n w) ∗ arcMetaOwn γ a v)) :=
  keep_pure (arcAuth_meta_agree γ a a' v v' n w)

theorem isArc_strong_pos (γ : GName) (a : Handle T) (v : T) (n w : Nat) :
    iprop(arcAuth (T := T) γ n w ∗ isArc γ a v) ⊢@{IProp GF} iprop(⌜1 ≤ n⌝) := by
  iintro ⟨HAuth, HA⟩
  iunfold arcAuth at HAuth
  icases HAuth with ⟨%a', %v', -, -, Hown⟩
  iunfold isArc at HA
  icases HA with ⟨%q, -, Hstrong, -⟩
  iapply arcAuth_strong_pos γ (some (a', v')) n w
  isplitl [Hown]
  · iexact Hown
  · iexact Hstrong

theorem isWeak_weak_pos (γ : GName) (a : Handle T) (v : T) (n w : Nat) :
    iprop(arcAuth (T := T) γ n w ∗ isWeak γ a v) ⊢@{IProp GF} iprop(⌜1 ≤ w⌝) := by
  iintro ⟨HAuth, HW⟩
  iunfold arcAuth at HAuth
  icases HAuth with ⟨%a', %v', -, -, Hown⟩
  iunfold isWeak at HW
  icases HW with ⟨-, Hweak⟩
  iapply arcAuth_weak_pos γ (some (a', v')) n w
  isplitl [Hown]
  · iexact Hown
  · iexact Hweak

theorem arcAuth_exclusive (γ : GName) (n₁ w₁ n₂ w₂ : Nat) :
    iprop(arcAuth (T := T) γ n₁ w₁ ∗ arcAuth (T := T) γ n₂ w₂)
      ⊢@{IProp GF} iprop(False) := by
  iintro ⟨H1, H2⟩
  iunfold arcAuth at H1
  iunfold arcAuth at H2
  icases H1 with ⟨%a₁, %v₁, -, -, Hown1⟩
  icases H2 with ⟨%a₂, %v₂, -, -, Hown2⟩
  ihave Hboth : iprop(iOwn (F := ArcF T) γ _ ∗ iOwn (F := ArcF T) γ _) $$ [Hown1 Hown2]
  · isplitl [Hown1]
    · iexact Hown1
    · iexact Hown2
  ihave %hv := iOwn_cmraValid_op $$ Hboth
  iexfalso
  ipureintro
  exact Auth.auth_op_valid.mp hv

theorem arcMetaOwn_agree (γ : GName) (a : Handle T) (v v' : T) :
    iprop(arcMetaOwn γ a v ∗ arcMetaOwn γ a v') ⊢@{IProp GF} iprop(⌜v = v'⌝) := by
  iintro ⟨H1, H2⟩
  simp only [arcMetaOwn] at *
  ihave Hboth : iprop(iOwn (F := ArcF T) γ _ ∗ iOwn (F := ArcF T) γ _) $$ [H1 H2]
  · isplitl [H1]
    · iexact H1
    · iexact H2
  ihave %hv := iOwn_cmraValid_op $$ Hboth
  ipureintro
  have hfrag : ✓{0} _ := (Auth.frag_op_valid.mp hv).validN
  simp only [res, CMRA.op, Prod.op] at hfrag
  obtain ⟨hmd, -⟩ := hfrag
  dsimp only at hmd
  have h : ✓{0} ((toAgree (LeibnizO.mk (a, v)) : Agree (ArcMeta T))
      • toAgree (LeibnizO.mk (a, v'))) := hmd
  have heq := Agree.toAgree_injN (Agree.Raw.op_invN h)
  have : (a, v) = (a, v') := LeibnizO.dist_inj heq
  grind

theorem isArc_agree (γ : GName) (a : Handle T) (v v' : T) :
    iprop(isArc γ a v ∗ isArc γ a v') ⊢@{IProp GF} iprop(⌜v = v'⌝) := by
  iintro ⟨H1, H2⟩
  iunfold isArc at H1
  iunfold isArc at H2
  icases H1 with ⟨%q₁, Hm1, -, -⟩
  icases H2 with ⟨%q₂, Hm2, -, -⟩
  iapply arcMetaOwn_agree γ a v v'
  isplitl [Hm1]
  · iexact Hm1
  · iexact Hm2

end Ghost

instance (a : Handle T) (n w : Nat) : Timeless (PROP := IProp GF) (physical a n w) := by
  cases n <;> cases w <;> (unfold physical; infer_instance)

section Timeless
variable [ArcG GF T]

instance arcAuth_timeless (γ : GName) (n w : Nat) :
    Timeless (PROP := IProp GF) (arcAuth (T := T) γ n w) := by
  unfold arcAuth
  refine @BI.exists_timeless _ _ _ _ ?_
  intro a
  refine @BI.exists_timeless _ _ _ _ ?_
  intro v
  cases n
  · dsimp only
    infer_instance
  · dsimp only
    infer_instance

instance isArc_timeless (γ : GName) (a : Handle T) (v : T) :
    Timeless (PROP := IProp GF) (isArc γ a v) := by
  unfold isArc arcMetaOwn arcStrongOwn
  refine @BI.exists_timeless _ _ _ _ ?_
  intro q
  infer_instance

instance isWeak_timeless (γ : GName) (a : Handle T) (v : T) :
    Timeless (PROP := IProp GF) (isWeak γ a v) := by
  unfold isWeak arcMetaOwn arcWeakOwn
  infer_instance

end Timeless

end Assertions

section Specs

open AeneasIris.ArcAPI
open AeneasIris.AtomicWpi

variable {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF] [HeapGS.{0} GF]
variable {E : Effect.{1}} [StateE RustHeap.{0} -< E] [StepE.{1} -< E]
variable {Hd : Handler E GF} [stateH heapInterp -<ₕ Hd]
variable {m : Mode} [stepH GF m -<ₕ Hd]
variable {T : Type} [Nonempty T] [ArcG GF T]

theorem new_spec (v : T) (M : CoPset) :
    ⦃ emp ⦄ (new (E := E) v) @ Hd ; m ; M
    ⦃ a, ∃ γ, arcAuth (T := T) γ 1 0 ∗ isArc γ a v ⦄ := by
  sorry

theorem deref_spec (γ : GName) (a : Handle T) (v : T) (M : CoPset) :
    ⦃ isArc γ a v ⦄ (deref (E := E) a) @ Hd ; m ; M
    ⦃ r, ⌜r = v⌝ ∗ isArc γ a v ⦄ := by
  show _ ⊢ _
  iintro HA
  simp only [isArc] at *
  icases HA with ⟨%q, Hmeta, Hstrong, Hpt⟩
  simp only [deref]
  istep
  isplitr
  itrivial
  iexists q
  iframe

/-- Opens with `iaupd_commit HAU as ⟨n, w⟩ with HAuth`; `arcAuth_strong_pos_keep`
then rules out `n = 0`, where `physical` owns no cells at all and the load would
have nothing to read, and `arcAuth_meta_agree_keep` identifies the authority's
handle with `a`. The counter-moving specs additionally need `Auth.auth_update`
with a `Credit` local update. -/
theorem strong_count_spec (γ : GName) (a : Handle T) (v : T) :
    ⊢ isArc γ a v -∗
      ⟪ ∀ n w, arcAuth (T := T) γ n w ⟫ Hd m (strong_count (E := E) a) @ (∅ : CoPset)
      ⟪ arcAuth (T := T) γ n w | RET (n : Int); isArc γ a v ⟫ := by
  sorry

theorem clone_spec (γ : GName) (a : Handle T) (v : T) :
    ⊢ isArc γ a v -∗
      ⟪ ∀ n w, arcAuth (T := T) γ n w ⟫ Hd m (clone (E := E) a) @ (∅ : CoPset)
      ⟪ arcAuth (T := T) γ (n + 1) w | RET a; isArc γ a v ∗ isArc γ a v ⟫ := by
  sorry

theorem downgrade_spec (γ : GName) (a : Handle T) (v : T) :
    ⊢ isArc γ a v -∗
      ⟪ ∀ n w, arcAuth (T := T) γ n w ⟫ Hd m (downgrade (E := E) a) @ (∅ : CoPset)
      ⟪ arcAuth (T := T) γ n (w + 1)
      | RET (WeakHandle.live a); isArc γ a v ∗ isWeak γ a v ⟫ := by
  sorry

theorem dropStrong_spec (γ : GName) (a : Handle T) (v : T) :
    ⊢ isArc γ a v -∗
      ⟪ ∀ n w, arcAuth (T := T) γ n w ⟫ Hd m (dropStrong (E := E) a) @ (∅ : CoPset)
      ⟪ arcAuth (T := T) γ (n - 1) (if n = 1 then w + 1 else w)
      | RET (decide (n = 1)); if n = 1 then isWeak γ a v else emp ⟫ := by
  sorry

theorem weakClone_spec (γ : GName) (a : Handle T) (v : T) :
    ⊢ isWeak γ a v -∗
      ⟪ ∀ n w, arcAuth (T := T) γ n w ⟫
        Hd m (weakClone (E := E) (.live a)) @ (∅ : CoPset)
      ⟪ arcAuth (T := T) γ n (w + 1)
      | RET (WeakHandle.live a); isWeak γ a v ∗ isWeak γ a v ⟫ := by
  sorry

theorem weakUpgrade_spec (γ : GName) (a : Handle T) (v : T) :
    ⊢ isWeak γ a v -∗
      ⟪ ∀ n w, arcAuth (T := T) γ n w ⟫
        Hd m (weakUpgrade (E := E) (.live a)) @ (∅ : CoPset)
      ⟪ arcAuth (T := T) γ (if n = 0 then 0 else n + 1) w
      | RET (if n = 0 then none else some a)
      ; isWeak γ a v ∗ (if n = 0 then emp else isArc γ a v) ⟫ := by
  sorry

theorem weakStrongCount_spec (γ : GName) (a : Handle T) (v : T) :
    ⊢ isWeak γ a v -∗
      ⟪ ∀ n w, arcAuth (T := T) γ n w ⟫
        Hd m (weakStrongCount (E := E) (.live a)) @ (∅ : CoPset)
      ⟪ arcAuth (T := T) γ n w | RET (n : Int); isWeak γ a v ⟫ := by
  sorry

theorem weakDrop_spec (γ : GName) (a : Handle T) (v : T) :
    ⊢ isWeak γ a v -∗
      ⟪ ∀ n w, arcAuth (T := T) γ n w ⟫
        Hd m (weakDrop (E := E) (.live a)) @ (∅ : CoPset)
      ⟪ arcAuth (T := T) γ n (w - 1) | RET () ⟫ := by
  sorry

omit [Nonempty T] [ArcG GF T] in
theorem dangling_clone_spec (M : CoPset) :
    ⦃ emp ⦄ (weakClone (E := E) (T := T) .dangling) @ Hd ; m ; M
    ⦃ r, ⌜r = WeakHandle.dangling⌝ ⦄ := by
  show _ ⊢ _
  simp only [weakClone]
  iintro _
  iapply wpi_ret
  itrivial

omit [Nonempty T] [ArcG GF T] in
theorem dangling_upgrade_spec (M : CoPset) :
    ⦃ emp ⦄ (weakUpgrade (E := E) (T := T) .dangling) @ Hd ; m ; M
    ⦃ r, ⌜r = none⌝ ⦄ := by
  show _ ⊢ _
  simp only [weakUpgrade]
  iintro _
  iapply wpi_ret
  itrivial

omit [Nonempty T] [ArcG GF T] in
theorem dangling_strong_count_spec (M : CoPset) :
    ⦃ emp ⦄ (weakStrongCount (E := E) (T := T) .dangling) @ Hd ; m ; M
    ⦃ r, ⌜r = 0⌝ ⦄ := by
  show _ ⊢ _
  simp only [weakStrongCount]
  iintro _
  iapply wpi_ret
  itrivial

omit [Nonempty T] [ArcG GF T] in
theorem dangling_drop_spec (M : CoPset) :
    ⦃ emp ⦄ (weakDrop (E := E) (T := T) .dangling) @ Hd ; m ; M
    ⦃ r, ⌜r = ()⌝ ⦄ := by
  show _ ⊢ _
  simp only [weakDrop]
  iintro _
  iapply wpi_ret
  itrivial

noncomputable instance instArcAPI :
    ArcAPI GF Hd m T (Handle T) (WeakHandle T) where
  new := new
  deref := deref
  strong_count := strong_count
  clone := clone
  downgrade := downgrade
  dropStrong := dropStrong
  weakClone := weakClone
  weakDrop := weakDrop
  weakUpgrade := weakUpgrade
  weakStrongCount := weakStrongCount

  weakNew := weakNew
  mkWeak := .live

  arcAuth := arcAuth
  isArc := isArc
  isWeak := isWeak

  weak_cases w := by cases w with
    | dangling => exact .inl rfl
    | live a => exact .inr ⟨a, rfl⟩
  arcAuth_timeless := by infer_instance
  isArc_timeless := by infer_instance
  isWeak_timeless := by infer_instance
  arcAuth_exclusive := arcAuth_exclusive
  isArc_agree := isArc_agree
  isArc_strong_pos := isArc_strong_pos
  isWeak_weak_pos := isWeak_weak_pos

  new_spec := new_spec
  deref_spec := deref_spec
  strong_count_spec := strong_count_spec
  clone_spec := clone_spec
  downgrade_spec := downgrade_spec
  dropStrong_spec := dropStrong_spec
  weakClone_spec := weakClone_spec
  weakUpgrade_spec := weakUpgrade_spec
  weakStrongCount_spec := weakStrongCount_spec
  weakDrop_spec := weakDrop_spec
  dangling_clone_spec := dangling_clone_spec
  dangling_upgrade_spec := dangling_upgrade_spec
  dangling_strong_count_spec := dangling_strong_count_spec
  dangling_drop_spec := dangling_drop_spec

end Specs

end AeneasIris.ArcImpl
