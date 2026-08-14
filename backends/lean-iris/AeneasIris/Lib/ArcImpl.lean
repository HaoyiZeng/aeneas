import AeneasIris.Lib.ArcAPI
import AeneasIris.Effects.HeapAPI
import AeneasIris.Effects.AtomicHeapAPI
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
variable [Aeneas.Std.ConcE.{1} -< E]
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

noncomputable def drop_strong (a : Handle T) : ITree E Bool := do
  let old : Int ← faa a.strong (-1)
  if old = 1 then
    let _ ← HeapAPI.free a.data
    return true
  else
    return false

def weak_new : WeakHandle T := .dangling

noncomputable def weak_clone (w : WeakHandle T) : ITree E (WeakHandle T) :=
  match w with
  | .dangling => ITree.ret .dangling
  | .live a => do
      let _ ← faa a.weak (1 : Int)
      return .live a

noncomputable def weak_drop (w : WeakHandle T) : ITree E Unit :=
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
noncomputable def try_upgrade (a : Handle T) : ITree E (Option (Handle T)) :=
  ITree.iter (fun _ => do
    let n : Int ← load a.strong
    if n = 0 then
      return .inr none
    else
      let ok ← cas a.strong n (n + 1)
      if ok then return .inr (some a) else return .inl ()) ()

noncomputable def weak_upgrade (w : WeakHandle T) : ITree E (Option (Handle T)) :=
  match w with
  | .dangling => ITree.ret none
  | .live a => try_upgrade a

noncomputable def weak_strong_count (w : WeakHandle T) : ITree E Int :=
  match w with
  | .dangling => ITree.ret 0
  | .live a => load a.strong

end Code

/-- A strictly positive count: positivity in the carrier, not in the validity. -/
def PosNat : Type := { n : Nat // 0 < n }

namespace PosNat

def val (x : PosNat) : Nat := x.1
theorem pos (x : PosNat) : 0 < x.val := x.2
theorem ext {x y : PosNat} (h : x.val = y.val) : x = y := Subtype.ext h
@[simp] theorem ext_iff {x y : PosNat} : x = y ↔ x.val = y.val := Subtype.ext_iff

instance : Add PosNat :=
  ⟨fun x y => ⟨x.val + y.val, by have := x.pos; have := y.pos; grind⟩⟩
instance : One PosNat := ⟨⟨1, by grind⟩⟩

@[simp] theorem val_add (x y : PosNat) : (x + y).val = x.val + y.val := rfl
@[simp] theorem val_one : (1 : PosNat).val = 1 := rfl

def ofSucc (n : Nat) : PosNat := ⟨n + 1, by grind⟩
@[simp] theorem ofSucc_val (n : Nat) : (ofSucc n).val = n + 1 := rfl
@[simp] theorem ofSucc_zero : ofSucc 0 = (1 : PosNat) := ext rfl

instance : COFE PosNat := COFE.ofDiscrete _ Eq_Equivalence
instance : OFE.Discrete PosNat := ⟨congrArg id⟩
instance : OFE.Leibniz PosNat := ⟨congrArg id⟩

instance : CMRA PosNat where
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
  assoc := OFE.leibniz.mpr <| ext (Nat.add_assoc ..).symm
  comm := OFE.leibniz.mpr <| ext (Nat.add_comm ..)
  pcore_op_left H := by rcases H
  pcore_idem H := by rcases H
  pcore_op_mono H := by rcases H
  extend {_ x y z} := by rintro _ rfl; exists y; exists z

instance : CMRA.Discrete PosNat where
  discrete_0 := id
  discrete_valid _ := trivial

@[simp] theorem op_eq (x y : PosNat) : x • y = x + y := rfl
@[simp] theorem valid (x : PosNat) : ✓ x := trivial

/-- The lemma shape that makes "at count one the frame must be `none`" derivable. -/
theorem not_incl_self (x : PosNat) : ¬ (x ≼ x) := by
  rintro ⟨c, hc⟩
  have h : x.val = x.val + c.val := congrArg Subtype.val hc
  have := c.pos
  grind

instance instCancelable {x : PosNat} : CMRA.Cancelable x where
  cancelableN {_n} {y} {z} _ h := by
    have h' : x.val + y.val = x.val + z.val := congrArg PosNat.val h
    exact ext (by grind)

end PosNat

instance instIdFreeQpPos {x : Qp × PosNat} : CMRA.IdFree x where
  id_free0_r y _ h := by
    have h2 : x.2 + y.2 = x.2 := h.2
    have hy := y.2.pos
    have h3 : x.2.val + y.2.val = x.2.val := congrArg PosNat.val h2
    grind

instance instCancelableQpPos {x : Qp × PosNat} : CMRA.Cancelable x where
  cancelableN hv h := ⟨CMRA.cancelableN hv.1 h.1, CMRA.cancelableN hv.2 h.2⟩

section Assertions

variable {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF] [G : HeapGS.{0} GF]
variable {T : Type}

/-- The control block. At `0, 0` the whole allocation is gone, so there are no
cells left to own -- which is why every spec first has to rule that case out. -/
def physical (a : Handle T) : Nat → Nat → IProp GF
  | 0, 0 => iprop(emp)
  | 0, (w + 1) => iprop(a.strong ↦ (0 : Int) ∗ a.weak ↦ ((w : Int) + 1))
  | (n + 1), w => iprop(a.strong ↦ ((n : Int) + 1) ∗ a.weak ↦ ((w : Int) + 1))

/-- The value in the weak cell: the strong references share one implicit weak. -/
def wcell (n k : Nat) : Int := if n = 0 then (k : Int) else (k : Int) + 1

theorem wcell_succ (n k : Nat) : wcell n (k + 1) = wcell n k + 1 := by
  unfold wcell; split <;> simp only [Nat.cast_add, Nat.cast_one]

theorem wcell_pred (n k : Nat) (h : 1 ≤ k) : wcell n (k - 1) = wcell n k - 1 := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by grind⟩
  simp only [Nat.add_sub_cancel, wcell_succ]; ring

theorem wcell_one_zero : wcell 1 0 = 1 := by decide

theorem wcell_of_ne (n n₂ k : Nat) (h : n ≠ 0) (h₂ : n₂ ≠ 0) : wcell n k = wcell n₂ k := by
  unfold wcell; simp only [if_neg h, if_neg h₂]

theorem physical_split (a : Handle T) (n k : Nat) (h : n = 0 → 1 ≤ k) :
    physical (GF := GF) a n k = iprop(a.strong ↦ (n : Int) ∗ a.weak ↦ wcell n k) := by
  cases n
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by have := h rfl; grind⟩
    simp only [physical, wcell, if_true, Nat.cast_zero, Nat.cast_add, Nat.cast_one]
  · simp only [physical, wcell, Nat.cast_add, Nat.cast_one,
      if_neg (Nat.succ_ne_zero _)]

abbrev ArcMeta (T : Type) := LeibnizO (Handle T × T)
abbrev ArcShare := Option (Qp × PosNat)
abbrev ArcRes (T : Type) :=
  ULift.{1} (Option (Agree (ArcMeta T)) × (Credit × (Credit × ArcShare)))
abbrev ArcF (T : Type) : COFE.OFunctorPre.{1,1,1} := Auth.AuthURF (constOF (ArcRes T))

class ArcG (GF : BundledGFunctors) (T : Type) where
  [arcG : ElemG GF (ArcF T)]

attribute [reducible, instance] ArcG.arcG

section Ghost
variable [ArcG GF T]

/-- Agreement, one credit per reference, and the strong share with its count. -/
def res (md : Option (Handle T × T)) (n w : Nat) (s : ArcShare) : ArcRes T :=
  ULift.up (md.map (fun x => toAgree (LeibnizO.mk x)), (n, (w, s)))

/-- The share slot is `none` exactly when no strong reference is left. -/
def shareOf : Nat → Qp → ArcShare
  | 0, _ => none
  | m + 1, q => some (q, PosNat.ofSucc m)

/-- What the authority keeps of the payload cell: the complement of `qs`. -/
def payloadOf (a : Handle T) (v : T) : Nat → Qp → IProp GF
  | 0, _ => iprop(emp)
  | _ + 1, qs => iprop(∃ qrest : Qp, ⌜qs + qrest = (1 : Qp)⌝ ∗
      pointsTo a.data (DFrac.own qrest) v)

@[simp] theorem shareOf_one (q : Qp) : shareOf 1 q = some (q, 1) := rfl

theorem shareOf_succ (m : Nat) (q : Qp) :
    shareOf (m + 1) q = some (q, PosNat.ofSucc m) := rfl

@[simp] theorem shareOf_zero (q : Qp) : shareOf 0 q = none := rfl

def arcAuth (γ : GName) (n w : Nat) : IProp GF := iprop(
  ∃ a : Handle T, ∃ v : T, ∃ qs : Qp,
    physical a n w ∗ payloadOf a v n qs ∗
    iOwn (F := ArcF T) γ (● res (some (a, v)) n w (shareOf n qs)))

def arcMetaOwn (γ : GName) (a : Handle T) (v : T) : IProp GF :=
  iprop(iOwn (F := ArcF T) γ (◯ res (some (a, v)) 0 0 none))

def arcStrongOwn (γ : GName) (q : Qp) : IProp GF :=
  iprop(iOwn (F := ArcF T) γ (◯ res (T := T) none 1 0 (some (q, 1))))

def arcWeakOwn (γ : GName) : IProp GF :=
  iprop(iOwn (F := ArcF T) γ (◯ res (T := T) none 0 1 none))

/-- One strong reference: agreement, a credit carrying `q`, and that share. -/
def isArc (γ : GName) (a : Handle T) (v : T) : IProp GF :=
  iprop(∃ q : Qp, arcMetaOwn γ a v ∗ arcStrongOwn (T := T) γ q ∗
    pointsTo a.data (DFrac.own q) v)

def isWeak (γ : GName) : WeakHandle T → T → IProp GF
  | .dangling, _ => iprop(False)
  | .live a, v => iprop(arcMetaOwn γ a v ∗ arcWeakOwn (T := T) γ)

/-- Pure, hence persistent: a dangling handle is a fact, not a permission. -/
def isDanglingWeak (w : WeakHandle T) : IProp GF := iprop(⌜w = .dangling⌝)

@[simp] theorem res_op (md : Option (Handle T × T)) (n w n' w' : Nat)
    (s s' : ArcShare) :
    res md n w s • res (T := T) none n' w' s' = res md (n + n') (w + w') (s • s') := by
  cases md <;> rfl

private theorem credit_lu {N d N' d' : Nat} (h : ∀ z, N = d + z → N' = d' + z) :
    ((N, d) : Credit × Credit) ~l~> (N', d') :=
  (local_update_unital_discrete N d N' d').mpr (fun z _ he => ⟨trivial, h z he⟩)

private theorem res_lu (md₁ md₂ : Option (Handle T × T)) (N K d e N' K' d' e' : Nat)
    (S s S' s' : ArcShare)
    (hn : ∀ z, N = d + z → N' = d' + z) (hk : ∀ z, K = e + z → K' = e' + z)
    (hs : ((S, s) : ArcShare × ArcShare) ~l~> (S', s')) :
    ((res md₁ N K S, res md₂ d e s) : ArcRes T × ArcRes T)
      ~l~> (res md₁ N' K' S', res md₂ d' e' s') :=
  Iris.Algebra.LocalUpdate.uLift
    (LocalUpdate.prod' (LocalUpdate.id _)
      (LocalUpdate.prod' (credit_lu hn) (LocalUpdate.prod' (credit_lu hk) hs)))

/-- A new reference takes its share out of `qrest`: `clone` and `weak_upgrade`. -/
private theorem share_alloc (qs p : Qp) (m : Nat) (hv : (p + qs).val ≤ 1) :
    ((some (qs, PosNat.ofSucc m), (none : ArcShare)) : ArcShare × ArcShare)
      ~l~> ((some (p, 1) : ArcShare) • some (qs, PosNat.ofSucc m), some (p, 1)) :=
  LocalUpdate.op (fun _ _ => ⟨hv, trivial⟩)

theorem share_alloc_eq (qs p : Qp) (m : Nat) :
    ((some (p, 1) : ArcShare) • some (qs, PosNat.ofSucc m))
      = shareOf (m + 1 + 1) (qs + p) := by
  have h1 : (p + qs) = qs + p := Subtype.ext (by simp only [Qp.val_add]; grind)
  have h2 : ((1 : PosNat) + PosNat.ofSucc m) = PosNat.ofSucc (m + 1) :=
    PosNat.ext (by simp only [PosNat.val_add, PosNat.val_one, PosNat.ofSucc_val]; grind)
  show (some ((p + qs), ((1 : PosNat) + PosNat.ofSucc m)) : ArcShare) = _
  simp only [shareOf, h1, h2]

/-- Dropping returns the share. The frame is what is left of the authority. -/
private theorem share_dealloc (q : Qp) (zs : ArcShare) :
    (((some (q, 1) : ArcShare) • zs, (some (q, 1) : ArcShare)) : ArcShare × ArcShare)
      ~l~> (zs, none) :=
  LocalUpdate.cancel _ zs none

/-- Given explicitly: synthesis times out looking for it through `ULift`,
`Option`, `Agree` and the pair. -/
instance arcMeta_coreId (a : Handle T) (v : T) :
    CMRA.CoreId (res (T := T) (some (a, v)) 0 0 none) := ⟨.rfl⟩

instance arcMetaOwn_persistent (γ : GName) (a : Handle T) (v : T) :
    Persistent (arcMetaOwn (GF := GF) γ a v) := by
  unfold arcMetaOwn
  infer_instance

/-- Holding a credit forces the matching count to be positive: `clone`/`drop`
learn they are not acting on a dead `Arc`, and they learn it from the *linear*
credit rather than from anything persistent. Read off, like the lock does, by
combining the two `iOwn`s and projecting `Auth.auth_both_valid`'s inclusion. -/
theorem arcAuth_strong_pos (γ : GName) (md : Option (Handle T × T)) (n w : Nat)
    (S : ArcShare) (q : Qp) :
    iprop(iOwn (F := ArcF T) γ (● res md n w S) ∗ arcStrongOwn (T := T) γ q)
      ⊢@{IProp GF} iprop(⌜1 ≤ n⌝) := by
  iintro ⟨H1, H2⟩
  simp only [arcStrongOwn] at *
  ihave Hboth : iprop(iOwn (F := ArcF T) γ _ ∗ iOwn (F := ArcF T) γ _) $$ [H1 H2]
  · isplitl [H1]
    · iexact H1
    · iexact H2
  ihave %hv := iOwn_cmraValid_op $$ Hboth
  ipureintro
  obtain ⟨⟨⟨zmd, zn, zw, zs⟩⟩, hz⟩ := (Auth.auth_both_valid.mp hv).1 0
  simp only [res, CMRA.op, Prod.op] at hz
  obtain ⟨-, hn, -, -⟩ := hz
  have hn' : n = 1 + zn := hn
  grind

theorem arcAuth_weak_pos (γ : GName) (md : Option (Handle T × T)) (n w : Nat)
    (S : ArcShare) :
    iprop(iOwn (F := ArcF T) γ (● res md n w S) ∗ arcWeakOwn (T := T) γ)
      ⊢@{IProp GF} iprop(⌜1 ≤ w⌝) := by
  iintro ⟨H1, H2⟩
  simp only [arcWeakOwn] at *
  ihave Hboth : iprop(iOwn (F := ArcF T) γ _ ∗ iOwn (F := ArcF T) γ _) $$ [H1 H2]
  · isplitl [H1]
    · iexact H1
    · iexact H2
  ihave %hv := iOwn_cmraValid_op $$ Hboth
  ipureintro
  obtain ⟨⟨⟨zmd, zn, zw, zs⟩⟩, hz⟩ := (Auth.auth_both_valid.mp hv).1 0
  simp only [res, CMRA.op, Prod.op] at hz
  obtain ⟨-, -, hw, -⟩ := hz
  have hw' : w = 1 + zw := hw
  grind

/-- The metadata fragment pins down which allocation and payload the ghost name
denotes: the slot is an `Agree`, so the fragment's entry is included in the
authority's, and inclusion between `toAgree`s is equality of the carriers. -/
theorem arcAuth_meta_agree (γ : GName) (a a' : Handle T) (v v' : T) (n w : Nat)
    (S : ArcShare) :
    iprop(iOwn (F := ArcF T) γ (● res (some (a', v')) n w S) ∗ arcMetaOwn γ a v)
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
  obtain ⟨⟨⟨zmd, zn, zw, zs⟩⟩, hz⟩ := hincl 0
  simp only [res, CMRA.op, Prod.op] at hz
  obtain ⟨hmd, -, -, -⟩ := hz
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

/-- At two or more references the frame exists: it is what the survivors keep. -/
theorem arcAuth_share_frame (γ : GName) (md : Option (Handle T × T)) (w m : Nat)
    (qs q : Qp) :
    iprop(iOwn (F := ArcF T) γ (● res md (m + 1 + 1) w (shareOf (m + 1 + 1) qs)) ∗
        arcStrongOwn (T := T) γ q)
      ⊢@{IProp GF} iprop(⌜∃ cq : Qp, qs = cq + q⌝) := by
  iintro ⟨H1, H2⟩
  simp only [arcStrongOwn] at *
  ihave Hboth : iprop(iOwn (F := ArcF T) γ _ ∗ iOwn (F := ArcF T) γ _) $$ [H1 H2]
  · isplitl [H1]
    · iexact H1
    · iexact H2
  ihave %hv := iOwn_cmraValid_op $$ Hboth
  ipureintro
  obtain ⟨⟨⟨zmd, zn, zw, zs⟩⟩, hz⟩ := (Auth.auth_both_valid.mp hv).1 0
  simp only [res, CMRA.op, Prod.op, shareOf] at hz
  obtain ⟨-, -, -, hs⟩ := hz
  cases zs
  · exfalso
    have h : ((qs, PosNat.ofSucc (m + 1)) : Qp × PosNat) ≡{0}≡ (q, (1 : PosNat)) := hs
    have h2 : PosNat.ofSucc (m + 1) = (1 : PosNat) := h.2
    have h3 := congrArg PosNat.val h2
    simp only [PosNat.ofSucc_val, PosNat.val_one] at h3
    grind
  · rename_i c
    refine ⟨c.1, ?_⟩
    have h : ((qs, PosNat.ofSucc (m + 1)) : Qp × PosNat) ≡{0}≡ ((q, (1 : PosNat)) • c) := hs
    have h1 : qs.val = q.val + c.1.val := Qp.dist_iff.mp h.1
    exact Subtype.ext (by simp only [Qp.val_add]; grind)

/-- The facts above are pure, so they can be read off without giving up the
resources they came from. `ihave ... $$ [H₁ H₂]` hands its arguments over, and
every caller still needs the authority in order to commit it. -/
private theorem keep_pure {P : IProp GF} {φ : Prop} (h : P ⊢ iprop(⌜φ⌝)) :
    P ⊢ iprop(⌜φ⌝ ∗ P) :=
  (BI.and_intro h .rfl).trans BI.persistent_and_sep_mp

theorem arcAuth_strong_pos_keep (γ : GName) (md : Option (Handle T × T)) (n w : Nat)
    (S : ArcShare) (q : Qp) :
    iprop(iOwn (F := ArcF T) γ (● res md n w S) ∗ arcStrongOwn (T := T) γ q)
      ⊢@{IProp GF} iprop(⌜1 ≤ n⌝ ∗
        (iOwn (F := ArcF T) γ (● res md n w S) ∗ arcStrongOwn (T := T) γ q)) :=
  keep_pure (arcAuth_strong_pos γ md n w S q)

theorem arcAuth_meta_agree_keep (γ : GName) (a a' : Handle T) (v v' : T) (n w : Nat)
    (S : ArcShare) :
    iprop(iOwn (F := ArcF T) γ (● res (some (a', v')) n w S) ∗ arcMetaOwn γ a v)
      ⊢@{IProp GF} iprop(⌜a' = a ∧ v' = v⌝ ∗
        (iOwn (F := ArcF T) γ (● res (some (a', v')) n w S) ∗ arcMetaOwn γ a v)) :=
  keep_pure (arcAuth_meta_agree γ a a' v v' n w S)

/-- At one reference the frame must be `none`, so the share is the holder's. -/
theorem arcAuth_share_agree (γ : GName) (md : Option (Handle T × T)) (n w : Nat)
    (qs q : Qp) (hn : n = 1) :
    iprop(iOwn (F := ArcF T) γ (● res md n w (shareOf n qs)) ∗
        arcStrongOwn (T := T) γ q)
      ⊢@{IProp GF} iprop(⌜qs = q⌝) := by
  subst hn
  iintro ⟨H1, H2⟩
  simp only [arcStrongOwn] at *
  ihave Hboth : iprop(iOwn (F := ArcF T) γ _ ∗ iOwn (F := ArcF T) γ _) $$ [H1 H2]
  · isplitl [H1]
    · iexact H1
    · iexact H2
  ihave %hv := iOwn_cmraValid_op $$ Hboth
  ipureintro
  obtain ⟨⟨⟨zmd, zn, zw, zs⟩⟩, hz⟩ := (Auth.auth_both_valid.mp hv).1 0
  simp only [res, CMRA.op, Prod.op, shareOf, PosNat.ofSucc_zero] at hz
  obtain ⟨-, -, -, hs⟩ := hz
  cases zs
  · have h : ((qs, (1 : PosNat)) : Qp × PosNat) ≡{0}≡ (q, (1 : PosNat)) := hs
    exact Subtype.ext (Qp.dist_iff.mp h.1)
  · rename_i c
    exfalso
    have h : ((qs, (1 : PosNat)) : Qp × PosNat) ≡{0}≡ ((q, (1 : PosNat)) • c) := hs
    have h2 : (1 : PosNat) = (1 : PosNat) + c.2 := h.2
    have h3 : (1 : Nat) = 1 + c.2.val := congrArg PosNat.val h2
    have := c.2.pos
    grind

theorem isArc_strong_pos (γ : GName) (a : Handle T) (v : T) (n w : Nat) :
    iprop(arcAuth (T := T) γ n w ∗ isArc γ a v) ⊢@{IProp GF} iprop(⌜1 ≤ n⌝) := by
  iintro ⟨HAuth, HA⟩
  iunfold arcAuth at HAuth
  icases HAuth with ⟨%a', %v', %qs, -, -, Hown⟩
  iunfold isArc at HA
  icases HA with ⟨%q, -, Hstrong, -⟩
  iapply arcAuth_strong_pos γ (some (a', v')) n w (shareOf n qs) q
  isplitl [Hown]
  · iexact Hown
  · iexact Hstrong

theorem isWeak_weak_pos (γ : GName) (wh : WeakHandle T) (v : T) (n k : Nat) :
    iprop(arcAuth (T := T) γ n k ∗ isWeak γ wh v) ⊢@{IProp GF} iprop(⌜1 ≤ k⌝) := by
  cases wh
  · simp only [isWeak]
    iintro ⟨-, HW⟩
    iexfalso; iexact HW
  · iintro ⟨HAuth, HW⟩
    iunfold arcAuth at HAuth
    icases HAuth with ⟨%a', %v', %qs, -, -, Hown⟩
    iunfold isWeak at HW
    icases HW with ⟨-, Hweak⟩
    iapply arcAuth_weak_pos γ (some (a', v')) n k (shareOf n qs)
    isplitl [Hown]
    · iexact Hown
    · iexact Hweak

theorem arc_update (γ : GName) (md₁ md₂ : Option (Handle T × T))
    (N K d e N' K' d' e' : Nat) (S s S' s' : ArcShare)
    (hn : ∀ z, N = d + z → N' = d' + z) (hk : ∀ z, K = e + z → K' = e' + z)
    (hs : ((S, s) : ArcShare × ArcShare) ~l~> (S', s')) :
    iprop(iOwn (F := ArcF T) γ (● res md₁ N K S) ∗
        iOwn (F := ArcF T) γ (◯ res md₂ d e s))
      ⊢@{IProp GF} iprop(|==> (iOwn (F := ArcF T) γ (● res md₁ N' K' S') ∗
          iOwn (F := ArcF T) γ (◯ res md₂ d' e' s'))) := by
  refine .trans (iOwn_update_op (GF := GF) (F := ArcF T) (γ := γ)
    (Auth.auth_update (res_lu md₁ md₂ N K d e N' K' d' e' S s S' s' hn hk hs))) ?_
  exact BIUpdate.mono (iOwn_op (GF := GF) (F := ArcF T) (γ := γ)).mp

theorem meta_dup (γ : GName) (a : Handle T) (v : T) :
    iprop(arcMetaOwn (GF := GF) γ a v) ⊢ iprop(arcMetaOwn γ a v ∗ arcMetaOwn γ a v) :=
  BI.persistent_entails_right .rfl

theorem frag_split (γ : GName) (md : Option (Handle T × T)) (d e d' e' : Nat)
    (s s' : ArcShare) :
    iprop(iOwn (F := ArcF T) γ (◯ res md (d + d') (e + e') (s • s')))
      ⊢@{IProp GF} iprop(iOwn (F := ArcF T) γ (◯ res md d e s) ∗
        iOwn (F := ArcF T) γ (◯ res (T := T) none d' e' s')) := by
  rw [show (◯ res md (d + d') (e + e') (s • s') : (ArcF T).ap (IProp GF))
        = (◯ res md d e s) • (◯ res (T := T) none d' e' s') from by
      rw [← Auth.frag_op, res_op]]
  exact iOwn_op.mp

/-- Peel the metadata fragment off a strong credit. -/
theorem frag_split_s (γ : GName) (a : Handle T) (v : T) (q : Qp) :
    iprop(iOwn (F := ArcF T) γ (◯ res (some (a, v)) 1 0 (some (q, 1))))
      ⊢@{IProp GF} iprop(iOwn (F := ArcF T) γ (◯ res (some (a, v)) 0 0 none) ∗
        iOwn (F := ArcF T) γ (◯ res (T := T) none 1 0 (some (q, 1)))) := by
  rw [show (◯ res (some (a, v)) 1 0 (some (q, 1)) : (ArcF T).ap (IProp GF))
        = (◯ res (some (a, v)) 0 0 none) • (◯ res (T := T) none 1 0 (some (q, 1))) from by
      rw [← Auth.frag_op, res_op]; rfl]
  exact iOwn_op.mp

theorem arc_isArc_facts (γ : GName) (a a' : Handle T) (v v' : T) (n k : Nat)
    (S : ArcShare) (q : Qp) :
    iprop(iOwn (F := ArcF T) γ (● res (some (a', v')) n k S) ∗ arcMetaOwn γ a v ∗
        arcStrongOwn (T := T) γ q)
      ⊢@{IProp GF} iprop(⌜a' = a ∧ v' = v ∧ 1 ≤ n⌝ ∗
        (iOwn (F := ArcF T) γ (● res (some (a', v')) n k S) ∗ arcMetaOwn γ a v ∗
          arcStrongOwn (T := T) γ q)) := by
  iintro ⟨Hown, Hmeta, Hstrong⟩
  ihave H1 : iprop(⌜a' = a ∧ v' = v⌝ ∗
      (iOwn (F := ArcF T) γ (● res (some (a', v')) n k S) ∗
      arcMetaOwn γ a v)) $$ [Hown Hmeta]
  · iapply arcAuth_meta_agree_keep
    isplitl [Hown]
    · iexact Hown
    · iexact Hmeta
  icases H1 with ⟨%hag, Hown, Hmeta⟩
  ihave H2 : iprop(⌜1 ≤ n⌝ ∗ (iOwn (F := ArcF T) γ (● res (some (a', v')) n k S) ∗
      arcStrongOwn (T := T) γ q)) $$ [Hown Hstrong]
  · iapply arcAuth_strong_pos_keep
    isplitl [Hown]
    · iexact Hown
    · iexact Hstrong
  icases H2 with ⟨%hpos, Hown, Hstrong⟩
  isplitl []
  · ipureintro; exact ⟨hag.1, hag.2, hpos⟩
  · isplitl [Hown]
    · iexact Hown
    · isplitl [Hmeta]
      · iexact Hmeta
      · iexact Hstrong

theorem arc_isWeak_facts (γ : GName) (a a' : Handle T) (v v' : T) (n k : Nat)
    (S : ArcShare) :
    iprop(iOwn (F := ArcF T) γ (● res (some (a', v')) n k S) ∗ arcMetaOwn γ a v ∗
        arcWeakOwn (T := T) γ)
      ⊢@{IProp GF} iprop(⌜a' = a ∧ v' = v ∧ 1 ≤ k⌝ ∗
        (iOwn (F := ArcF T) γ (● res (some (a', v')) n k S) ∗ arcMetaOwn γ a v ∗
          arcWeakOwn (T := T) γ)) := by
  iintro ⟨Hown, Hmeta, Hweak⟩
  ihave H1 : iprop(⌜a' = a ∧ v' = v⌝ ∗
      (iOwn (F := ArcF T) γ (● res (some (a', v')) n k S) ∗
      arcMetaOwn γ a v)) $$ [Hown Hmeta]
  · iapply arcAuth_meta_agree_keep
    isplitl [Hown]
    · iexact Hown
    · iexact Hmeta
  icases H1 with ⟨%hag, Hown, Hmeta⟩
  ihave H2 : iprop(⌜1 ≤ k⌝ ∗ (iOwn (F := ArcF T) γ (● res (some (a', v')) n k S) ∗
      arcWeakOwn (T := T) γ)) $$ [Hown Hweak]
  · iapply (keep_pure (arcAuth_weak_pos γ (some (a', v')) n k S))
    isplitl [Hown]
    · iexact Hown
    · iexact Hweak
  icases H2 with ⟨%hpos, Hown, Hweak⟩
  isplitl []
  · ipureintro; exact ⟨hag.1, hag.2, hpos⟩
  · isplitl [Hown]
    · iexact Hown
    · isplitl [Hmeta]
      · iexact Hmeta
      · iexact Hweak

theorem data_split (a : Handle T) (v : T) (q : Qp) :
    iprop(pointsTo (GF := GF) a.data (DFrac.own q) v)
      ⊢@{IProp GF} iprop(pointsTo a.data (DFrac.own q.half) v ∗
        pointsTo a.data (DFrac.own q.half) v) := by
  have h := (Iris.Fractional.fractional
    (Φ := fun r : Qp => pointsTo (GF := GF) a.data (DFrac.own r) v) q.half q.half).1
  rw [Qp.half_add_half] at h
  exact h

theorem arcAuth_exclusive (γ : GName) (n₁ w₁ n₂ w₂ : Nat) :
    iprop(arcAuth (T := T) γ n₁ w₁ ∗ arcAuth (T := T) γ n₂ w₂)
      ⊢@{IProp GF} iprop(False) := by
  iintro ⟨H1, H2⟩
  iunfold arcAuth at H1
  iunfold arcAuth at H2
  icases H1 with ⟨%a₁, %v₁, %qs₁, -, -, Hown1⟩
  icases H2 with ⟨%a₂, %v₂, %qs₂, -, -, Hown2⟩
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
  refine @BI.exists_timeless _ _ _ _ ?_
  intro qs
  cases n
  · dsimp only [payloadOf]
    infer_instance
  · dsimp only [payloadOf]
    infer_instance

instance isArc_timeless (γ : GName) (a : Handle T) (v : T) :
    Timeless (PROP := IProp GF) (isArc γ a v) := by
  unfold isArc arcMetaOwn arcStrongOwn
  refine @BI.exists_timeless _ _ _ _ ?_
  intro q
  infer_instance

instance isWeak_timeless (γ : GName) (wh : WeakHandle T) (v : T) :
    Timeless (PROP := IProp GF) (isWeak γ wh v) := by
  cases wh <;> (unfold isWeak arcMetaOwn arcWeakOwn; infer_instance)

instance isDanglingWeak_persistent (wh : WeakHandle T) :
    Persistent (PROP := IProp GF) (isDanglingWeak wh) := by
  unfold isDanglingWeak; infer_instance

theorem isWeak_not_dangling (γ : GName) (wh : WeakHandle T) (v : T) :
    iprop(isWeak γ wh v ∗ isDanglingWeak wh) ⊢@{IProp GF} iprop(False) := by
  cases wh
  · simp only [isWeak]; iintro ⟨HW, -⟩; iexfalso; iexact HW
  · simp only [isDanglingWeak]; iintro ⟨-, %h⟩; exact absurd h (by simp)

end Timeless

end Assertions

section Specs

open AeneasIris.AtomicWpi

variable {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF] [HeapGS.{0} GF]
variable {E : Effect.{1}} [StateE RustHeap.{0} -< E] [StepE.{1} -< E]
variable [Aeneas.Std.ConcE.{1} -< E]
variable {Hd : Handler E GF} [stateH heapInterp -<ₕ Hd]
variable {m : Mode} [stepH GF m -<ₕ Hd]
variable {T : Type} [Nonempty T] [ArcG GF T]

theorem new_spec (v : T) (M : CoPset) :
    ⦃ emp ⦄ (new (E := E) v) @ Hd ; m ; M
    ⦃ a, ∃ γ, arcAuth (T := T) γ 1 0 ∗ isArc γ a v ⦄ := by
  show _ ⊢ _
  iintro _
  simp only [new]
  ibind
  iapply (HeapAPI.wpi_alloc (Hd := Hd) (m := m) (E := E) (1 : Int))
  iapply (AeneasIris.Step.lat_intro m _)
  iintro %ls Hs
  imodintro
  ibind
  iapply (HeapAPI.wpi_alloc (Hd := Hd) (m := m) (E := E) (1 : Int))
  iapply (AeneasIris.Step.lat_intro m _)
  iintro %lw Hw
  imodintro
  ibind
  iapply (HeapAPI.wpi_alloc (Hd := Hd) (m := m) (E := E) v)
  iapply (AeneasIris.Step.lat_intro m _)
  iintro %ld Hdata
  imod (iOwn_alloc (GF := GF) (F := ArcF T)
      ((● res (some ((⟨ls, lw, ld⟩ : Handle T), v)) 1 0 (some ((1 : Qp).half, 1))) •
        (◯ res (some ((⟨ls, lw, ld⟩ : Handle T), v)) 1 0 (some ((1 : Qp).half, 1))))
      (Auth.auth_both_valid_2
        ⟨Agree.toAgree_valid, trivial, trivial,
          (by grind), trivial⟩
        (CMRA.inc_refl _))) with ⟨%γ, Hg⟩
  ihave Hgs : iprop(iOwn (F := ArcF T) γ
        (● res (some ((⟨ls, lw, ld⟩ : Handle T), v)) 1 0 (some ((1 : Qp).half, 1))) ∗
      iOwn (F := ArcF T) γ
        (◯ res (some ((⟨ls, lw, ld⟩ : Handle T), v)) 1 0 (some ((1 : Qp).half, 1)))) $$ [Hg]
  · iapply (iOwn_op (GF := GF) (F := ArcF T) (γ := γ)).mp
    iexact Hg
  icases Hgs with ⟨Hown, Hfrag⟩
  ihave Hsplit : iprop(iOwn (F := ArcF T) γ
        (◯ res (some ((⟨ls, lw, ld⟩ : Handle T), v)) 0 0 none) ∗
      iOwn (F := ArcF T) γ (◯ res (T := T) none 1 0 (some ((1 : Qp).half, 1)))) $$ [Hfrag]
  · iapply frag_split_s
    iexact Hfrag
  icases Hsplit with ⟨Hmeta, Hstrong⟩
  ihave HD : iprop(pointsTo (⟨ls, lw, ld⟩ : Handle T).data (DFrac.own (1 : Qp).half) v ∗
      pointsTo (⟨ls, lw, ld⟩ : Handle T).data (DFrac.own (1 : Qp).half) v) $$ [Hdata]
  · iapply (data_split (⟨ls, lw, ld⟩ : Handle T) v 1)
    iexact Hdata
  icases HD with ⟨Hd1, Hd2⟩
  imodintro
  iret
  iexists γ
  isplitl [Hs Hw Hd1 Hown]
  · iunfold arcAuth
    iexists (⟨ls, lw, ld⟩ : Handle T)
    iexists v
    iexists (1 : Qp).half
    simp only [physical_split (⟨ls, lw, ld⟩ : Handle T) 1 0 (by grind), wcell_one_zero,
      Nat.cast_one, shareOf_one]
    isplitl [Hs Hw]
    · isplitl [Hs]
      · iexact Hs
      · iexact Hw
    · isplitl [Hd1]
      · iunfold payloadOf
        iexists (1 : Qp).half
        isplitl []
        · ipureintro
          exact Qp.half_add_half 1
        · iexact Hd1
      · iexact Hown
  · iunfold isArc
    iexists (1 : Qp).half
    isplitl [Hmeta]
    · iunfold arcMetaOwn
      iexact Hmeta
    · isplitl [Hstrong]
      · iunfold arcStrongOwn
        iexact Hstrong
      · iexact Hd2

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

theorem strong_count_spec (γ : GName) (a : Handle T) (v : T) :
    ⊢ isArc γ a v -∗
      ⟪ ∀ n k, arcAuth (T := T) γ n k ⟫ Hd m (strong_count (E := E) a) @ (∅ : CoPset)
      ⟪ arcAuth (T := T) γ n k | RET (n : Int); isArc γ a v ⟫ := by
  iintro HA
  simp only [atomicWpi]
  iintro %Φ HAU
  simp only [strong_count]
  iaupd_commit HAU as ⟨n, k⟩ with HAuth
  iunfold arcAuth at HAuth
  icases HAuth with ⟨%a', %v', %qs, Hphys, Hpay, Hown⟩
  iunfold isArc at HA
  icases HA with ⟨%q, Hmeta, Hstrong, Hdata⟩
  ihave Hf : iprop(⌜a' = a ∧ v' = v ∧ 1 ≤ n⌝ ∗
      (iOwn (F := ArcF T) γ (● res (some (a', v')) n k (shareOf n qs)) ∗
        arcMetaOwn γ a v ∗ arcStrongOwn (T := T) γ q)) $$ [Hown Hmeta Hstrong]
  · iapply arc_isArc_facts
    isplitl [Hown]
    · iexact Hown
    · isplitl [Hmeta]
      · iexact Hmeta
      · iexact Hstrong
  icases Hf with ⟨%hf, Hown, Hmeta, Hstrong⟩
  obtain ⟨rfl, rfl, hpos⟩ := hf
  simp only [physical_split a' n k (by grind)]
  icases Hphys with ⟨Hs, Hw⟩
  iapply (HeapAPI.wpi_load (Hd := Hd) (m := m) (E := E) a'.strong (n : Int) (DFrac.own 1))
  iapply (AeneasIris.Step.lat_intro m _)
  isplitl [Hs]
  · iexact Hs
  · iintro Hs2
    imodintro
    iexists ()
    isplitl [Hs2 Hw Hpay Hown]
    · iunfold arcAuth
      iexists a'
      iexists v'
      iexists qs
      simp only [physical_split a' n k (by grind)]
      isplitl [Hs2 Hw]
      · isplitl [Hs2]
        · iexact Hs2
        · iexact Hw
      · isplitl [Hpay]
        · iexact Hpay
        · iexact Hown
    · iintro HΨ
      simp only [AtomicWpi.wandM_some]
      iapply HΨ
      · exact ()
      · iunfold isArc
        iexists q
        isplitl [Hmeta]
        · iexact Hmeta
        · isplitl [Hstrong]
          · iexact Hstrong
          · iexact Hdata

theorem clone_spec (γ : GName) (a : Handle T) (v : T) :
    ⊢ isArc γ a v -∗
      ⟪ ∀ n k, arcAuth (T := T) γ n k ⟫ Hd m (clone (E := E) a) @ (∅ : CoPset)
      ⟪ arcAuth (T := T) γ (n + 1) k | RET a; isArc γ a v ∗ isArc γ a v ⟫ := by
  iintro HA
  simp only [atomicWpi]
  iintro %Φ HAU
  simp only [clone]
  ibind
  iaupd_commit HAU as ⟨n, k⟩ with HAuth
  iunfold arcAuth at HAuth
  icases HAuth with ⟨%a', %v', %qs, Hphys, Hpay, Hown⟩
  iunfold isArc at HA
  icases HA with ⟨%q, Hmeta, Hstrong, Hdata⟩
  ihave Hf : iprop(⌜a' = a ∧ v' = v ∧ 1 ≤ n⌝ ∗
      (iOwn (F := ArcF T) γ (● res (some (a', v')) n k (shareOf n qs)) ∗
        arcMetaOwn γ a v ∗ arcStrongOwn (T := T) γ q)) $$ [Hown Hmeta Hstrong]
  · iapply arc_isArc_facts
    isplitl [Hown]
    · iexact Hown
    · isplitl [Hmeta]
      · iexact Hmeta
      · iexact Hstrong
  icases Hf with ⟨%hf, Hown, Hmeta, Hstrong⟩
  obtain ⟨rfl, rfl, hpos⟩ := hf
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by grind⟩
  simp only [physical_split a' (n' + 1) k (by grind)]
  icases Hphys with ⟨Hs, Hw⟩
  iunfold payloadOf at Hpay
  icases Hpay with ⟨%qr, %hsum, Hpd⟩
  iapply (HeapAPI.wpi_faa (Hd := Hd) (m := m) (E := E) a'.strong (((n' + 1 : Nat) : Int)) 1)
  iapply (AeneasIris.Step.lat_intro m _)
  isplitl [Hs]
  · iexact Hs
  · iintro Hs2
    iunfold arcMetaOwn at Hmeta
    ihave Hpair : iprop(iOwn (F := ArcF T) γ
          (● res (some (a', v')) (n' + 1) k (shareOf (n' + 1) qs)) ∗
        iOwn (F := ArcF T) γ (◯ res (some (a', v')) 0 0 none)) $$ [Hown Hmeta]
    · isplitl [Hown]
      · iexact Hown
      · iexact Hmeta
    imod (arc_update γ (some (a', v')) (some (a', v')) (n' + 1) k 0 0 (n' + 1 + 1) k
      1 0 (shareOf (n' + 1) qs) none
      ((some (qr.half, 1) : ArcShare) • some (qs, PosNat.ofSucc n')) (some (qr.half, 1))
      (by grind) (by grind)
      (share_alloc qs qr.half n'
        (by have h1 := congrArg Subtype.val hsum
            have h2 := qr.2
            simp only [Qp.val_add, Qp.val_half, Qp.val_one] at h1 ⊢
            grind))) $$ Hpair with ⟨Hown, Hfrag⟩
    ihave Hsplit : iprop(iOwn (F := ArcF T) γ (◯ res (some (a', v')) 0 0 none) ∗
        iOwn (F := ArcF T) γ (◯ res (T := T) none 1 0 (some (qr.half, 1)))) $$ [Hfrag]
    · iapply frag_split_s
      iexact Hfrag
    icases Hsplit with ⟨Hmeta2, Hstrong2⟩
    ihave HM : iprop(arcMetaOwn γ a' v' ∗ arcMetaOwn γ a' v') $$ [Hmeta2]
    · iapply meta_dup
      iunfold arcMetaOwn
      iexact Hmeta2
    icases HM with ⟨Hm1, Hm2⟩
    ihave HD : iprop(pointsTo a'.data (DFrac.own qr.half) v' ∗
        pointsTo a'.data (DFrac.own qr.half) v') $$ [Hpd]
    · iapply (data_split a' v' qr)
      iexact Hpd
    icases HD with ⟨Hd1, Hd2⟩
    imodintro
    iexists ()
    isplitl [Hs2 Hw Hd1 Hown]
    · iunfold arcAuth
      iexists a'
      iexists v'
      iexists (qs + qr.half)
      simp only [physical_split a' (n' + 1 + 1) k (by grind),
        wcell_of_ne (n' + 1 + 1) (n' + 1) k (by grind) (by grind),
        Nat.cast_add, Nat.cast_one]
      isplitl [Hs2 Hw]
      · isplitl [Hs2]
        · iexact Hs2
        · iexact Hw
      · isplitl [Hd1]
        · iunfold payloadOf
          iexists qr.half
          isplitl []
          · ipureintro
            refine Subtype.ext ?_
            have h1 := congrArg Subtype.val hsum
            simp only [Qp.val_add, Qp.val_half, Qp.val_one] at h1 ⊢
            grind
          · iexact Hd1
        · simp only [share_alloc_eq]
          iexact Hown
    · iintro HΨ
      iret
      simp only [AtomicWpi.wandM_some]
      iapply HΨ
      · exact ()
      · isplitl [Hm1 Hstrong Hdata]
        · iunfold isArc
          iexists q
          isplitl [Hm1]
          · iexact Hm1
          · isplitl [Hstrong]
            · iexact Hstrong
            · iexact Hdata
        · iunfold isArc
          iexists qr.half
          isplitl [Hm2]
          · iexact Hm2
          · isplitl [Hstrong2]
            · iunfold arcStrongOwn
              iexact Hstrong2
            · iexact Hd2

theorem downgrade_spec (γ : GName) (a : Handle T) (v : T) :
    ⊢ isArc γ a v -∗
      ⟪ ∀ n k, arcAuth (T := T) γ n k ⟫ Hd m (downgrade (E := E) a) @ (∅ : CoPset)
      ⟪ arcAuth (T := T) γ n (k + 1)
      | w, RET w; isArc γ a v ∗ isWeak γ w v ⟫ := by
  iintro HA
  simp only [atomicWpi]
  iintro %Φ HAU
  simp only [downgrade]
  ibind
  iaupd_commit HAU as ⟨n, k⟩ with HAuth
  iunfold arcAuth at HAuth
  icases HAuth with ⟨%a', %v', %qs, Hphys, Hpay, Hown⟩
  iunfold isArc at HA
  icases HA with ⟨%q, Hmeta, Hstrong, Hdata⟩
  ihave Hf : iprop(⌜a' = a ∧ v' = v ∧ 1 ≤ n⌝ ∗
      (iOwn (F := ArcF T) γ (● res (some (a', v')) n k (shareOf n qs)) ∗
        arcMetaOwn γ a v ∗ arcStrongOwn (T := T) γ q)) $$ [Hown Hmeta Hstrong]
  · iapply arc_isArc_facts
    isplitl [Hown]
    · iexact Hown
    · isplitl [Hmeta]
      · iexact Hmeta
      · iexact Hstrong
  icases Hf with ⟨%hf, Hown, Hmeta, Hstrong⟩
  obtain ⟨rfl, rfl, hpos⟩ := hf
  simp only [physical_split a' n k (by grind)]
  icases Hphys with ⟨Hs, Hw⟩
  iapply (HeapAPI.wpi_faa (Hd := Hd) (m := m) (E := E) a'.weak (wcell n k) 1)
  iapply (AeneasIris.Step.lat_intro m _)
  isplitl [Hw]
  · iexact Hw
  · iintro Hw2
    iunfold arcMetaOwn at Hmeta
    ihave Hpair : iprop(iOwn (F := ArcF T) γ (● res (some (a', v')) n k (shareOf n qs)) ∗
        iOwn (F := ArcF T) γ (◯ res (some (a', v')) 0 0 none)) $$ [Hown Hmeta]
    · isplitl [Hown]
      · iexact Hown
      · iexact Hmeta
    imod (arc_update γ (some (a', v')) (some (a', v')) n k 0 0 n (k + 1)
      (0 + 0) (0 + 1) (shareOf n qs) none (shareOf n qs) ((none : ArcShare) • none)
      (by grind) (by grind) (LocalUpdate.id _)) $$ Hpair with ⟨Hown, Hfrag⟩
    ihave Hsplit : iprop(iOwn (F := ArcF T) γ (◯ res (some (a', v')) 0 0 none) ∗
        iOwn (F := ArcF T) γ (◯ res (T := T) none 0 1 none)) $$ [Hfrag]
    · iapply frag_split
      iexact Hfrag
    icases Hsplit with ⟨Hmeta, Hwk⟩
    ihave HM : iprop(arcMetaOwn γ a' v' ∗ arcMetaOwn γ a' v') $$ [Hmeta]
    · iapply meta_dup
      iunfold arcMetaOwn
      iexact Hmeta
    icases HM with ⟨Hm1, Hm2⟩
    imodintro
    iexists ()
    isplitl [Hs Hw2 Hpay Hown]
    · iunfold arcAuth
      iexists a'
      iexists v'
      iexists qs
      simp only [physical_split a' n (k + 1) (by grind), wcell_succ]
      isplitl [Hs Hw2]
      · isplitl [Hs]
        · iexact Hs
        · iexact Hw2
      · isplitl [Hpay]
        · iexact Hpay
        · iexact Hown
    · iintro HΨ
      iret
      simp only [AtomicWpi.wandM_some]
      iapply HΨ
      isplitl [Hm1 Hstrong Hdata]
      · iunfold isArc
        iexists q
        isplitl [Hm1]
        · iexact Hm1
        · isplitl [Hstrong]
          · iexact Hstrong
          · iexact Hdata
      · iunfold isWeak
        isplitl [Hm2]
        · iexact Hm2
        · iunfold arcWeakOwn
          iexact Hwk

theorem drop_strong_spec (γ : GName) (a : Handle T) (v : T) :
    ⊢ isArc γ a v -∗
      ⟪ ∀ n k, arcAuth (T := T) γ n k ⟫ Hd m (drop_strong (E := E) a) @ (∅ : CoPset)
      ⟪ arcAuth (T := T) γ (n - 1) (if n = 1 then k + 1 else k)
      | w, RET (decide (n = 1)); if n = 1 then isWeak γ w v else emp ⟫ := by
  iintro HA
  simp only [atomicWpi]
  iintro %Φ HAU
  simp only [drop_strong]
  ibind
  iaupd_commit HAU as ⟨n, k⟩ with HAuth
  iunfold arcAuth at HAuth
  icases HAuth with ⟨%a', %v', %qs, Hphys, Hpay, Hown⟩
  iunfold isArc at HA
  icases HA with ⟨%q, Hmeta, Hstrong, Hdata⟩
  ihave Hf : iprop(⌜a' = a ∧ v' = v ∧ 1 ≤ n⌝ ∗
      (iOwn (F := ArcF T) γ (● res (some (a', v')) n k (shareOf n qs)) ∗
        arcMetaOwn γ a v ∗ arcStrongOwn (T := T) γ q)) $$ [Hown Hmeta Hstrong]
  · iapply arc_isArc_facts
    isplitl [Hown]
    · iexact Hown
    · isplitl [Hmeta]
      · iexact Hmeta
      · iexact Hstrong
  icases Hf with ⟨%hf, Hown, Hmeta, Hstrong⟩
  obtain ⟨rfl, rfl, hpos⟩ := hf
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by grind⟩
  simp only [physical_split a' (n' + 1) k (by grind)]
  icases Hphys with ⟨Hs, Hw⟩
  iunfold payloadOf at Hpay
  icases Hpay with ⟨%qr, %hsum, Hpd⟩
  iapply (HeapAPI.wpi_faa (Hd := Hd) (m := m) (E := E) a'.strong (((n' + 1 : Nat) : Int)) (-1))
  iapply (AeneasIris.Step.lat_intro m _)
  isplitl [Hs]
  · iexact Hs
  · iintro Hs2
    by_cases hn1 : n' = 0
    · ihave Hqs : iprop(⌜qs = q⌝ ∗
          (iOwn (F := ArcF T) γ (● res (some (a', v')) (n' + 1) k (shareOf (n' + 1) qs)) ∗
            arcStrongOwn (T := T) γ q)) $$ [Hown Hstrong]
      · iapply (keep_pure (arcAuth_share_agree γ (some (a', v')) (n' + 1) k qs q
          (by grind)))
        isplitl [Hown]
        · iexact Hown
        · iexact Hstrong
      icases Hqs with ⟨%hqs, Hown, Hstrong⟩
      subst hqs
      have hshare : shareOf (n' + 1) qs = some (qs, 1) := by rw [hn1]; rfl
      have hEq : arcAuth (GF := GF) (T := T) γ (n' + 1 - 1)
            (if n' + 1 = 1 then k + 1 else k)
          = arcAuth (GF := GF) (T := T) γ 0 (k + 1) := by
        rw [if_pos (show n' + 1 = 1 from by grind), hn1]
      have hret : decide (n' + 1 = 1) = true := by grind
      have hpost : ∀ z : WeakHandle T,
          (if n' + 1 = 1 then isWeak (GF := GF) γ z v' else iprop(emp))
            = isWeak γ z v' := fun _ => if_pos (by grind)
      have hsv : ((n' + 1 : Nat) : Int) + -1 = ((0 : Nat) : Int) := by
        rw [hn1]; norm_num
      have hwc : wcell 0 (k + 1) = wcell (n' + 1) k := by
        rw [hn1]; unfold wcell; push_cast; norm_num
      ihave Hfull : iprop(pointsTo a'.data (DFrac.own (qs + qr)) v') $$ [Hdata Hpd]
      · iapply (HeapAPI.pointsTo_split a'.data qs qr v').mpr
        isplitl [Hdata]
        · iexact Hdata
        · iexact Hpd
      simp only [hsum, hshare]
      iunfold arcStrongOwn at Hstrong
      ihave Hpair : iprop(iOwn (F := ArcF T) γ
            (● res (some (a', v')) (n' + 1) k (some (qs, 1))) ∗
          iOwn (F := ArcF T) γ (◯ res (T := T) none 1 0 (some (qs, 1)))) $$ [Hown Hstrong]
      · isplitl [Hown]
        · iexact Hown
        · iexact Hstrong
      imod (arc_update γ (some (a', v')) none (n' + 1) k 1 0 0 (k + 1) 0 1
        (some (qs, 1) : ArcShare) (some (qs, 1)) none none
        (by grind) (by grind) (share_dealloc qs none)) $$ Hpair with ⟨Hown, Hfrag⟩
      imodintro
      iexists ()
      isplitl [Hs2 Hw Hown]
      · simp only [hEq]
        iunfold arcAuth
        iexists a'
        iexists v'
        iexists qs
        simp only [physical_split a' 0 (k + 1) (by grind), hwc, hsv, shareOf_zero]
        isplitl [Hs2 Hw]
        · isplitl [Hs2]
          · iexact Hs2
          · iexact Hw
        · isplitl []
          · iunfold payloadOf
            itrivial
          · iexact Hown
      · iintro HΨ
        simp only [if_pos (show ((n' + 1 : Nat) : Int) = 1 from by
          rw [hn1]; norm_num)]
        ibind
        iapply (HeapAPI.wpi_free (Hd := Hd) (m := m) (E := E) a'.data v')
        iapply (AeneasIris.Step.lat_intro m _)
        isplitl [Hfull]
        · iexact Hfull
        · imodintro
          iret
          simp only [hret, hpost, AtomicWpi.wandM_some]
          iapply HΨ $$ %(WeakHandle.live a')
          iunfold isWeak
          isplitl [Hmeta]
          · iexact Hmeta
          · iunfold arcWeakOwn
            iexact Hfrag
    · obtain ⟨mm, rfl⟩ : ∃ mm, n' = mm + 1 := ⟨n' - 1, by grind⟩
      ihave Hfr : iprop(⌜∃ cq : Qp, qs = cq + q⌝ ∗
          (iOwn (F := ArcF T) γ (● res (some (a', v')) (mm + 1 + 1) k
            (shareOf (mm + 1 + 1) qs)) ∗ arcStrongOwn (T := T) γ q)) $$ [Hown Hstrong]
      · iapply (keep_pure (arcAuth_share_frame γ (some (a', v')) k mm qs q))
        isplitl [Hown]
        · iexact Hown
        · iexact Hstrong
      icases Hfr with ⟨%hfr, Hown, Hstrong⟩
      obtain ⟨cq, rfl⟩ := hfr
      have hEq2 : arcAuth (GF := GF) (T := T) γ (mm + 1 + 1 - 1)
            (if mm + 1 + 1 = 1 then k + 1 else k)
          = arcAuth (GF := GF) (T := T) γ (mm + 1) k := by
        rw [if_neg (show ¬(mm + 1 + 1 = 1) from by grind), Nat.add_sub_cancel]
      have hdec2 : decide (mm + 1 + 1 = 1) = false := by grind
      have hpost2 : ∀ z : WeakHandle T,
          (if mm + 1 + 1 = 1 then isWeak (GF := GF) γ z v' else iprop(emp)) = iprop(emp) :=
        fun _ => if_neg (by grind)
      have hsh := (share_alloc_eq cq q mm).symm
      simp only [hsh]
      iunfold arcStrongOwn at Hstrong
      ihave Hpair : iprop(iOwn (F := ArcF T) γ (● res (some (a', v')) (mm + 1 + 1) k
            ((some (q, 1) : ArcShare) • some (cq, PosNat.ofSucc mm))) ∗
          iOwn (F := ArcF T) γ (◯ res (T := T) none 1 0 (some (q, 1)))) $$ [Hown Hstrong]
      · isplitl [Hown]
        · iexact Hown
        · iexact Hstrong
      imod (arc_update γ (some (a', v')) none (mm + 1 + 1) k 1 0 (mm + 1) k 0 0
        ((some (q, 1) : ArcShare) • some (cq, PosNat.ofSucc mm)) (some (q, 1))
        (some (cq, PosNat.ofSucc mm)) none
        (by grind) (by grind) (share_dealloc q _)) $$ Hpair with ⟨Hown, Hfrag⟩
      ihave Hrest : iprop(pointsTo a'.data (DFrac.own (qr + q)) v') $$ [Hdata Hpd]
      · iapply (HeapAPI.pointsTo_split a'.data qr q v').mpr
        isplitl [Hpd]
        · iexact Hpd
        · iexact Hdata
      imodintro
      iexists ()
      isplitl [Hs2 Hw Hrest Hown]
      · simp only [hEq2]
        iunfold arcAuth
        iexists a'
        iexists v'
        iexists cq
        isplitl [Hs2 Hw]
        · have hsv : ((mm + 1 + 1 : Nat) : Int) + -1 = ((mm + 1 : Nat) : Int) := by
            push_cast; ring
          simp only [physical_split a' (mm + 1) k (by grind),
            wcell_of_ne (mm + 1) (mm + 1 + 1) k (by grind) (by grind), hsv]
          isplitl [Hs2]
          · iexact Hs2
          · iexact Hw
        · isplitl [Hrest]
          · iunfold payloadOf
            iexists (qr + q)
            isplitl []
            · ipureintro
              refine Subtype.ext ?_
              have h1 := congrArg Subtype.val hsum
              simp only [Qp.val_add, Qp.val_one] at h1 ⊢
              grind
            · iexact Hrest
          · simp only [shareOf_succ]
            iexact Hown
      · iintro HΨ
        simp only [if_neg (show ¬(((mm + 1 + 1 : Nat) : Int) = 1) from by
          push_cast; grind)]
        iret
        simp only [hdec2, hpost2, AtomicWpi.wandM_some]
        iapply HΨ $$ %(WeakHandle.live a')
        itrivial

theorem weak_clone_spec (γ : GName) (w : WeakHandle T) (v : T) :
    ⊢ isWeak γ w v -∗
      ⟪ ∀ n k, arcAuth (T := T) γ n k ⟫
        Hd m (weak_clone (E := E) w) @ (∅ : CoPset)
      ⟪ arcAuth (T := T) γ n (k + 1)
      | RET w; isWeak γ w v ∗ isWeak γ w v ⟫ := by
  cases w
  · simp only [isWeak]
    iintro HW
    iexfalso
    iexact HW
  · rename_i a
    iintro HW
    simp only [atomicWpi]
    iintro %Φ HAU
    simp only [weak_clone]
    ibind
    iaupd_commit HAU as ⟨n, k⟩ with HAuth
    iunfold arcAuth at HAuth
    icases HAuth with ⟨%a', %v', %qs, Hphys, Hpay, Hown⟩
    iunfold isWeak at HW
    icases HW with ⟨Hmeta, Hweak⟩
    ihave Hf : iprop(⌜a' = a ∧ v' = v ∧ 1 ≤ k⌝ ∗
        (iOwn (F := ArcF T) γ (● res (some (a', v')) n k (shareOf n qs)) ∗
          arcMetaOwn γ a v ∗ arcWeakOwn (T := T) γ)) $$ [Hown Hmeta Hweak]
    · iapply arc_isWeak_facts
      isplitl [Hown]
      · iexact Hown
      · isplitl [Hmeta]
        · iexact Hmeta
        · iexact Hweak
    icases Hf with ⟨%hf, Hown, Hmeta, Hweak⟩
    obtain ⟨rfl, rfl, hpos⟩ := hf
    simp only [physical_split a' n k (by grind)]
    icases Hphys with ⟨Hs, Hw⟩
    iapply (HeapAPI.wpi_faa (Hd := Hd) (m := m) (E := E) a'.weak (wcell n k) 1)
    iapply (AeneasIris.Step.lat_intro m _)
    isplitl [Hw]
    · iexact Hw
    · iintro Hw2
      iunfold arcWeakOwn at Hweak
      ihave Hpair : iprop(iOwn (F := ArcF T) γ (● res (some (a', v')) n k (shareOf n qs)) ∗
          iOwn (F := ArcF T) γ (◯ res (T := T) none 0 1 none)) $$ [Hown Hweak]
      · isplitl [Hown]
        · iexact Hown
        · iexact Hweak
      imod (arc_update γ (some (a', v')) none n k 0 1 n (k + 1) (0 + 0) (1 + 1)
        (shareOf n qs) none (shareOf n qs) ((none : ArcShare) • none)
        (by grind) (by grind) (LocalUpdate.id _)) $$ Hpair with ⟨Hown, Hfrag⟩
      ihave Hsplit : iprop(iOwn (F := ArcF T) γ (◯ res (T := T) none 0 1 none) ∗
          iOwn (F := ArcF T) γ (◯ res (T := T) none 0 1 none)) $$ [Hfrag]
      · iapply frag_split
        iexact Hfrag
      icases Hsplit with ⟨Hk1, Hk2⟩
      ihave HM : iprop(arcMetaOwn γ a' v' ∗ arcMetaOwn γ a' v') $$ [Hmeta]
      · iapply meta_dup
        iexact Hmeta
      icases HM with ⟨Hm1, Hm2⟩
      imodintro
      iexists ()
      isplitl [Hs Hw2 Hpay Hown]
      · iunfold arcAuth
        iexists a'
        iexists v'
        iexists qs
        simp only [physical_split a' n (k + 1) (by grind), wcell_succ]
        isplitl [Hs Hw2]
        · isplitl [Hs]
          · iexact Hs
          · iexact Hw2
        · isplitl [Hpay]
          · iexact Hpay
          · iexact Hown
      · iintro HΨ
        iret
        simp only [AtomicWpi.wandM_some]
        iapply HΨ
        · exact ()
        · isplitl [Hm1 Hk1]
          · iunfold isWeak
            isplitl [Hm1]
            · iexact Hm1
            · iunfold arcWeakOwn
              iexact Hk1
          · iunfold isWeak
            isplitl [Hm2]
            · iexact Hm2
            · iunfold arcWeakOwn
              iexact Hk2

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

theorem weak_upgrade_spec [stepH GF Mode.part -<ₕ Hd]
    (γ : GName) (w : WeakHandle T) (v : T) :
    ⊢ isWeak γ w v -∗
      ⟪ ∀ n k, arcAuth (T := T) γ n k ⟫
        Hd Mode.part (weak_upgrade (E := E) w) @ (∅ : CoPset)
      ⟪ arcAuth (T := T) γ (if n = 0 then 0 else n + 1) k
      | a, RET (if n = 0 then none else some a)
      ; isWeak γ w v ∗ (if n = 0 then emp else isArc γ a v) ⟫ := by
  cases w
  · simp only [isWeak]
    iintro HW
    iexfalso
    iexact HW
  · rename_i a0
    iintro HW
    simp only [atomicWpi]
    iintro %Φ HAU
    simp only [weak_upgrade, try_upgrade]
    iloeb as IH
    iunfold ITree.iter
    ibind
    ibind
    iapply (wpi_aupd_choose (m := Mode.part) (hsub := by aupd_mask)) $$ HAU
    iintro %pk HAuth
    obtain ⟨n, k⟩ := pk
    iunfold arcAuth at HAuth
    icases HAuth with ⟨%a', %v', %qs, Hphys, Hpay, Hown⟩
    iunfold isWeak at HW
    icases HW with ⟨Hmeta, Hweak⟩
    ihave Hf : iprop(⌜a' = a0 ∧ v' = v ∧ 1 ≤ k⌝ ∗
        (iOwn (F := ArcF T) γ (● res (some (a', v')) n k (shareOf n qs)) ∗
          arcMetaOwn γ a0 v ∗ arcWeakOwn (T := T) γ)) $$ [Hown Hmeta Hweak]
    · iapply arc_isWeak_facts
      isplitl [Hown]
      · iexact Hown
      · isplitl [Hmeta]
        · iexact Hmeta
        · iexact Hweak
    icases Hf with ⟨%hf, Hown, Hmeta, Hweak⟩
    obtain ⟨rfl, rfl, hpos⟩ := hf
    simp only [physical_split a' n k (by grind)]
    icases Hphys with ⟨Hs, Hw⟩
    iapply (HeapAPI.wpi_load (Hd := Hd) (m := Mode.part) (E := E) a'.strong (n : Int)
      (DFrac.own 1))
    ilat
    inext
    isplitl [Hs]
    · iexact Hs
    · iintro Hs
      imodintro
      by_cases hn0 : n = 0
      · have hEq : arcAuth (GF := GF) (T := T) γ (if n = 0 then 0 else n + 1) k
            = arcAuth (GF := GF) (T := T) γ n k := by rw [if_pos hn0, hn0]
        have hprog : ∀ A B : ITree E (Unit ⊕ Option (Handle T)),
            (if ((n : Nat) : Int) = 0 then A else B) = A :=
          fun _ _ => if_pos (by grind)
        have hret : ∀ z : Handle T, (if n = 0 then none else some z) = none :=
          fun _ => if_pos hn0
        have hpost : ∀ z : Handle T,
            (if n = 0 then iprop(emp) else isArc (GF := GF) γ z v') = iprop(emp) :=
          fun _ => if_pos hn0
        iright
        iexists ()
        isplitl [Hs Hw Hpay Hown]
        · simp only [hEq]
          iunfold arcAuth
          iexists a'
          iexists v'
          iexists qs
          isplitl [Hs Hw]
          · simp only [physical_split a' n k (fun _ => hpos)]
            isplitl [Hs]
            · iexact Hs
            · iexact Hw
          · isplitl [Hpay]
            · iexact Hpay
            · iexact Hown
        · iintro HΨ
          simp only [hprog]
          iret
          iret
          simp only [hret, hpost, AtomicWpi.wandM_some]
          iapply HΨ $$ %a'
          isplitl [Hmeta Hweak]
          · iunfold isWeak
            isplitl [Hmeta]
            · iexact Hmeta
            · iexact Hweak
          · itrivial
      · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by grind⟩
        ileft
        isplitl [Hs Hw Hpay Hown]
        · iunfold arcAuth
          iexists a'
          iexists v'
          iexists qs
          isplitl [Hs Hw]
          · simp only [physical_split a' (n' + 1) k (by grind)]
            isplitl [Hs]
            · iexact Hs
            · iexact Hw
          · isplitl [Hpay]
            · iexact Hpay
            · iexact Hown
        · iintro HAU
          simp only [if_neg (show ¬(((n' + 1 : Nat) : Int) = 0) from by grind)]
          ibind
          iapply (wpi_aupd_choose (m := Mode.part) (hsub := by aupd_mask)) $$ HAU
          iintro %pk2 HAuth2
          obtain ⟨n₂, k₂⟩ := pk2
          iunfold arcAuth at HAuth2
          icases HAuth2 with ⟨%a₂, %v₂, %qs₂, Hphys2, Hpay2, Hown2⟩
          ihave Hf2 : iprop(⌜a₂ = a' ∧ v₂ = v' ∧ 1 ≤ k₂⌝ ∗
              (iOwn (F := ArcF T) γ (● res (some (a₂, v₂)) n₂ k₂ (shareOf n₂ qs₂)) ∗
                arcMetaOwn γ a' v' ∗ arcWeakOwn (T := T) γ)) $$ [Hown2 Hmeta Hweak]
          · iapply arc_isWeak_facts
            isplitl [Hown2]
            · iexact Hown2
            · isplitl [Hmeta]
              · iexact Hmeta
              · iexact Hweak
          icases Hf2 with ⟨%hf2, Hown2, Hmeta, Hweak⟩
          obtain ⟨rfl, rfl, hpos2⟩ := hf2
          simp only [physical_split a₂ n₂ k₂ (by grind)]
          icases Hphys2 with ⟨Hs2, Hw2⟩
          by_cases hne : n₂ = n' + 1
          · subst hne
            have hEq2 : arcAuth (GF := GF) (T := T) γ
                  (if n' + 1 = 0 then 0 else n' + 1 + 1) k₂
                = arcAuth (GF := GF) (T := T) γ (n' + 1 + 1) k₂ := by
              rw [if_neg (show ¬((n' + 1) = 0) from by grind)]
            iapply (HeapAPI.wpi_cas_succ (Hd := Hd) (m := Mode.part) (E := E) a₂.strong
              (((n' + 1 : Nat) : Int)) (((n' + 1 : Nat) : Int) + 1))
            iapply (AeneasIris.Step.lat_intro Mode.part _)
            isplitl [Hs2]
            · iexact Hs2
            · iintro Hs2
              iunfold arcMetaOwn at Hmeta
              iunfold payloadOf at Hpay2
              icases Hpay2 with ⟨%qr, %hsum, Hpd⟩
              ihave Hpair : iprop(iOwn (F := ArcF T) γ
                    (● res (some (a₂, v₂)) (n' + 1) k₂ (shareOf (n' + 1) qs₂)) ∗
                  iOwn (F := ArcF T) γ (◯ res (some (a₂, v₂)) 0 0 none)) $$ [Hown2 Hmeta]
              · isplitl [Hown2]
                · iexact Hown2
                · iexact Hmeta
              imod (arc_update γ (some (a₂, v₂)) (some (a₂, v₂)) (n' + 1) k₂ 0 0
                (n' + 1 + 1) k₂ 1 0 (shareOf (n' + 1) qs₂) none
                ((some (qr.half, 1) : ArcShare) • some (qs₂, PosNat.ofSucc n'))
                (some (qr.half, 1)) (by grind) (by grind)
                (share_alloc qs₂ qr.half n'
                  (by have h1 := congrArg Subtype.val hsum
                      have h2 := qr.2
                      simp only [Qp.val_add, Qp.val_half, Qp.val_one] at h1 ⊢
                      grind))) $$ Hpair with ⟨Hown2, Hfrag⟩
              ihave Hsplit : iprop(iOwn (F := ArcF T) γ (◯ res (some (a₂, v₂)) 0 0 none) ∗
                  iOwn (F := ArcF T) γ (◯ res (T := T) none 1 0 (some (qr.half, 1))))
                  $$ [Hfrag]
              · iapply frag_split_s
                iexact Hfrag
              icases Hsplit with ⟨Hmeta2, Hstrong⟩
              ihave HM : iprop(arcMetaOwn γ a₂ v₂ ∗ arcMetaOwn γ a₂ v₂) $$ [Hmeta2]
              · iapply meta_dup
                iunfold arcMetaOwn
                iexact Hmeta2
              icases HM with ⟨Hm1, Hm2⟩
              ihave HD : iprop(pointsTo a₂.data (DFrac.own qr.half) v₂ ∗
                  pointsTo a₂.data (DFrac.own qr.half) v₂) $$ [Hpd]
              · iapply (data_split a₂ v₂ qr)
                iexact Hpd
              icases HD with ⟨Hd1, Hd2⟩
              imodintro
              iright
              iexists ()
              isplitl [Hs2 Hw2 Hd1 Hown2]
              · simp only [hEq2]
                iunfold arcAuth
                iexists a₂
                iexists v₂
                iexists (qs₂ + qr.half)
                isplitl [Hs2 Hw2]
                · simp only [physical_split a₂ (n' + 1 + 1) k₂ (by grind),
                    wcell_of_ne (n' + 1 + 1) (n' + 1) k₂ (by grind) (by grind),
                    Nat.cast_add, Nat.cast_one]
                  isplitl [Hs2]
                  · iexact Hs2
                  · iexact Hw2
                · isplitl [Hd1]
                  · iunfold payloadOf
                    iexists qr.half
                    isplitl []
                    · ipureintro
                      refine Subtype.ext ?_
                      have h1 := congrArg Subtype.val hsum
                      simp only [Qp.val_add, Qp.val_half, Qp.val_one] at h1 ⊢
                      grind
                    · iexact Hd1
                  · simp only [share_alloc_eq]
                    iexact Hown2
              · iintro HΨ
                simp only [reduceIte]
                iret
                iret
                simp only [AtomicWpi.wandM_some,
                  if_neg (show ¬((n' + 1) = 0) from by grind)]
                iapply HΨ $$ %a₂
                isplitl [Hm1 Hweak]
                · iunfold isWeak
                  isplitl [Hm1]
                  · iexact Hm1
                  · iexact Hweak
                · iunfold isArc
                  iexists qr.half
                  isplitl [Hm2]
                  · iexact Hm2
                  · isplitl [Hstrong]
                    · iunfold arcStrongOwn
                      iexact Hstrong
                    · iexact Hd2
          · iapply (HeapAPI.wpi_cas_fail (Hd := Hd) (m := Mode.part) (E := E) a₂.strong
              ((n₂ : Int)) (((n' + 1 : Nat) : Int)) (((n' + 1 : Nat) : Int) + 1)
              (DFrac.own 1) (by intro hc; exact hne (by exact_mod_cast hc)))
            iapply (AeneasIris.Step.lat_intro Mode.part _)
            isplitl [Hs2]
            · iexact Hs2
            · iintro Hs2
              imodintro
              ileft
              isplitl [Hs2 Hw2 Hpay2 Hown2]
              · iunfold arcAuth
                iexists a₂
                iexists v₂
                iexists qs₂
                isplitl [Hs2 Hw2]
                · simp only [physical_split a₂ n₂ k₂ (by grind)]
                  isplitl [Hs2]
                  · iexact Hs2
                  · iexact Hw2
                · isplitl [Hpay2]
                  · iexact Hpay2
                  · iexact Hown2
              · iintro HAU
                simp only [Bool.false_eq_true, if_false]
                iret
                ihave HWn : isWeak γ (WeakHandle.live a₂) v₂ $$ [Hmeta Hweak]
                · iunfold isWeak
                  isplitl [Hmeta]
                  · iexact Hmeta
                  · iexact Hweak
                iapply IH $$ HWn HAU

theorem weak_strong_count_spec (γ : GName) (w : WeakHandle T) (v : T) :
    ⊢ isWeak γ w v -∗
      ⟪ ∀ n k, arcAuth (T := T) γ n k ⟫
        Hd m (weak_strong_count (E := E) w) @ (∅ : CoPset)
      ⟪ arcAuth (T := T) γ n k | RET (n : Int); isWeak γ w v ⟫ := by
  cases w
  · simp only [isWeak]
    iintro HW
    iexfalso
    iexact HW
  · rename_i a
    iintro HW
    simp only [atomicWpi]
    iintro %Φ HAU
    simp only [weak_strong_count]
    iaupd_commit HAU as ⟨n, k⟩ with HAuth
    iunfold arcAuth at HAuth
    icases HAuth with ⟨%a', %v', %qs, Hphys, Hpay, Hown⟩
    iunfold isWeak at HW
    icases HW with ⟨Hmeta, Hweak⟩
    ihave Hf : iprop(⌜a' = a ∧ v' = v ∧ 1 ≤ k⌝ ∗
        (iOwn (F := ArcF T) γ (● res (some (a', v')) n k (shareOf n qs)) ∗
          arcMetaOwn γ a v ∗ arcWeakOwn (T := T) γ)) $$ [Hown Hmeta Hweak]
    · iapply arc_isWeak_facts
      isplitl [Hown]
      · iexact Hown
      · isplitl [Hmeta]
        · iexact Hmeta
        · iexact Hweak
    icases Hf with ⟨%hf, Hown, Hmeta, Hweak⟩
    obtain ⟨rfl, rfl, hpos⟩ := hf
    simp only [physical_split a' n k (by grind)]
    icases Hphys with ⟨Hs, Hw⟩
    iapply (HeapAPI.wpi_load (Hd := Hd) (m := m) (E := E) a'.strong (n : Int) (DFrac.own 1))
    iapply (AeneasIris.Step.lat_intro m _)
    isplitl [Hs]
    · iexact Hs
    · iintro Hs2
      imodintro
      iexists ()
      isplitl [Hs2 Hw Hpay Hown]
      · iunfold arcAuth
        iexists a'
        iexists v'
        iexists qs
        simp only [physical_split a' n k (by grind)]
        isplitl [Hs2 Hw]
        · isplitl [Hs2]
          · iexact Hs2
          · iexact Hw
        · isplitl [Hpay]
          · iexact Hpay
          · iexact Hown
      · iintro HΨ
        simp only [AtomicWpi.wandM_some]
        iapply HΨ
        · exact ()
        · iunfold isWeak
          isplitl [Hmeta]
          · iexact Hmeta
          · iexact Hweak

theorem weak_drop_spec (γ : GName) (w : WeakHandle T) (v : T) :
    ⊢ isWeak γ w v -∗
      ⟪ ∀ n k, arcAuth (T := T) γ n k ⟫
        Hd m (weak_drop (E := E) w) @ (∅ : CoPset)
      ⟪ arcAuth (T := T) γ n (k - 1) | RET () ⟫ := by
  cases w
  · simp only [isWeak]
    iintro HW
    iexfalso
    iexact HW
  · rename_i a
    iintro HW
    simp only [atomicWpi]
    iintro %Φ HAU
    simp only [weak_drop]
    ibind
    iaupd_commit HAU as ⟨n, k⟩ with HAuth
    iunfold arcAuth at HAuth
    icases HAuth with ⟨%a', %v', %qs, Hphys, Hpay, Hown⟩
    iunfold isWeak at HW
    icases HW with ⟨Hmeta, Hweak⟩
    ihave Hf : iprop(⌜a' = a ∧ v' = v ∧ 1 ≤ k⌝ ∗
        (iOwn (F := ArcF T) γ (● res (some (a', v')) n k (shareOf n qs)) ∗
          arcMetaOwn γ a v ∗ arcWeakOwn (T := T) γ)) $$ [Hown Hmeta Hweak]
    · iapply arc_isWeak_facts
      isplitl [Hown]
      · iexact Hown
      · isplitl [Hmeta]
        · iexact Hmeta
        · iexact Hweak
    icases Hf with ⟨%hf, Hown, Hmeta, Hweak⟩
    obtain ⟨rfl, rfl, hpos⟩ := hf
    simp only [physical_split a' n k (by grind)]
    icases Hphys with ⟨Hs, Hw⟩
    iapply (HeapAPI.wpi_faa (Hd := Hd) (m := m) (E := E) a'.weak (wcell n k) (-1))
    iapply (AeneasIris.Step.lat_intro m _)
    isplitl [Hw]
    · iexact Hw
    · iintro Hw2
      iunfold arcWeakOwn at Hweak
      ihave Hpair : iprop(iOwn (F := ArcF T) γ (● res (some (a', v')) n k (shareOf n qs)) ∗
          iOwn (F := ArcF T) γ (◯ res (T := T) none 0 1 none)) $$ [Hown Hweak]
      · isplitl [Hown]
        · iexact Hown
        · iexact Hweak
      imod (arc_update γ (some (a', v')) none n k 0 1 n (k - 1) (0 + 0) (0 + 0)
        (shareOf n qs) none (shareOf n qs) ((none : ArcShare) • none)
        (by grind) (by grind) (LocalUpdate.id _)) $$ Hpair with ⟨Hown, Hfrag⟩
      imodintro
      by_cases hone : wcell n k = 1
      · have hnk : n = 0 ∧ k = 1 := by
          by_cases h0 : n = 0
          · subst h0
            simp only [wcell, if_true] at hone
            grind
          · exfalso
            simp only [wcell, if_neg h0] at hone
            grind
        obtain ⟨rfl, rfl⟩ := hnk
        iexists ()
        isplitl [Hown]
        · iunfold arcAuth
          iexists a'
          iexists v'
          iexists qs
          simp only [Nat.sub_self]
          iunfold physical
          isplitl []
          · itrivial
          · isplitl []
            · iunfold payloadOf
              itrivial
            · iexact Hown
        · iintro HΨ
          simp only [if_pos hone]
          ibind
          iapply (HeapAPI.wpi_free (Hd := Hd) (m := m) (E := E) a'.strong ((0 : Nat) : Int))
          iapply (AeneasIris.Step.lat_intro m _)
          isplitl [Hs]
          · iexact Hs
          · imodintro
            iapply (HeapAPI.wpi_free (Hd := Hd) (m := m) (E := E) a'.weak (wcell 0 1 + -1))
            iapply (AeneasIris.Step.lat_intro m _)
            isplitl [Hw2]
            · iexact Hw2
            · imodintro
              simp only [AtomicWpi.wandM_none]
              iapply HΨ $$ %()
      · iexists ()
        isplitl [Hs Hw2 Hpay Hown]
        · iunfold arcAuth
          iexists a'
          iexists v'
          iexists qs
          simp only [physical_split a' n (k - 1)
              (by intro h0; subst h0; simp only [wcell, if_true] at hone; grind),
            wcell_pred n k hpos, sub_eq_add_neg]
          isplitl [Hs Hw2]
          · isplitl [Hs]
            · iexact Hs
            · iexact Hw2
          · isplitl [Hpay]
            · iexact Hpay
            · iexact Hown
        · iintro HΨ
          simp only [if_neg hone]
          iret
          simp only [AtomicWpi.wandM_none]
          iapply HΨ $$ %()

omit [Nonempty T] [ArcG GF T] in
theorem dangling_clone_spec (w : WeakHandle T) (M : CoPset) :
    ⦃ isDanglingWeak (GF := GF) w ⦄ (weak_clone (E := E) w) @ Hd ; m ; M
    ⦃ r, ⌜r = w⌝ ∗ isDanglingWeak w ⦄ := by
  show _ ⊢ _
  simp only [isDanglingWeak]
  iintro %hw
  subst hw
  simp only [weak_clone]
  iapply wpi_ret
  itrivial

omit [Nonempty T] [ArcG GF T] in
theorem dangling_upgrade_spec (w : WeakHandle T) (M : CoPset) :
    ⦃ isDanglingWeak (GF := GF) w ⦄ (weak_upgrade (E := E) w) @ Hd ; m ; M
    ⦃ r, ⌜r = none⌝ ⦄ := by
  show _ ⊢ _
  simp only [isDanglingWeak]
  iintro %hw
  subst hw
  simp only [weak_upgrade]
  iapply wpi_ret
  itrivial

omit [Nonempty T] [ArcG GF T] in
theorem dangling_strong_count_spec (w : WeakHandle T) (M : CoPset) :
    ⦃ isDanglingWeak (GF := GF) w ⦄ (weak_strong_count (E := E) w) @ Hd ; m ; M
    ⦃ r, ⌜r = 0⌝ ⦄ := by
  show _ ⊢ _
  simp only [isDanglingWeak]
  iintro %hw
  subst hw
  simp only [weak_strong_count]
  iapply wpi_ret
  itrivial

omit [Nonempty T] [ArcG GF T] in
theorem dangling_drop_spec (w : WeakHandle T) (M : CoPset) :
    ⦃ isDanglingWeak (GF := GF) w ⦄ (weak_drop (E := E) w) @ Hd ; m ; M
    ⦃ _r, emp ⦄ := by
  show _ ⊢ _
  simp only [isDanglingWeak]
  iintro %hw
  subst hw
  simp only [weak_drop]
  iapply wpi_ret
  itrivial

noncomputable instance instArcAPI [stepH GF Mode.part -<ₕ Hd] :
    ArcAPI GF Hd m T (Handle T) (WeakHandle T) where
  new := new
  deref := deref
  strong_count := strong_count
  clone := clone
  downgrade := downgrade
  drop_strong := drop_strong
  weak_clone := weak_clone
  weak_drop := weak_drop
  weak_upgrade := weak_upgrade
  weak_strong_count := weak_strong_count

  weak_new := weak_new

  arcAuth := arcAuth
  isArc := isArc
  isWeak := isWeak
  isDanglingWeak := isDanglingWeak

  arcAuth_timeless := by infer_instance
  isArc_timeless := by infer_instance
  isWeak_timeless := by infer_instance
  isDanglingWeak_persistent := by infer_instance
  weak_new_dangling := by simp only [isDanglingWeak, weak_new]; itrivial
  arcAuth_exclusive := arcAuth_exclusive
  isArc_agree := isArc_agree
  isArc_strong_pos := isArc_strong_pos
  isWeak_weak_pos := isWeak_weak_pos
  isWeak_not_dangling := isWeak_not_dangling

  new_spec := new_spec
  deref_spec := deref_spec
  strong_count_spec := strong_count_spec
  clone_spec := clone_spec
  downgrade_spec := downgrade_spec
  drop_strong_spec := drop_strong_spec
  weak_clone_spec := weak_clone_spec
  weak_upgrade_spec := weak_upgrade_spec
  weak_strong_count_spec := weak_strong_count_spec
  weak_drop_spec := weak_drop_spec
  dangling_clone_spec := dangling_clone_spec
  dangling_upgrade_spec := dangling_upgrade_spec
  dangling_strong_count_spec := dangling_strong_count_spec
  dangling_drop_spec := dangling_drop_spec

end Specs

end AeneasIris.ArcImpl
