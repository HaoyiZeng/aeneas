import AeneasIris.Lib.ArcImpl
import AeneasIris.Effects.AtomicHeapAPI

/-! # The ITree `Arc` over an atomic heap

The reference counts are `AtomicUsize` in Rust, so every access to one is a point
at which another thread may act.  This implementation reads and writes them
through `AtomicHeapAPI`, which yields before each access; `ArcImpl` reads them
through the plain heap, which does not.

The ghost state is `ArcImpl`'s, unchanged: what a thread owns does not depend on
where the interference points are.  Only the programs and their proofs differ.

Unqualified operations are the atomic ones -- that is the norm here.  The two
plain-heap uses are qualified, and are deliberate: allocation is unreachable by
another thread until the handle is published, and `deref` reads the payload,
which is not an atomic in Rust either. -/

unseal Aeneas.Std.Result

namespace AeneasIris.AtomicArcImpl

open Iris BI Aeneas.Data.Coinductive
open AeneasIris AeneasIris.AtomicHeapAPI
open AeneasIris.ArcImpl (Handle WeakHandle)
open Aeneas.Std (StateE StepE Loc Val RustHeap)
open scoped Aeneas.Std
open AeneasIris.Step (lat stepH)
open Iris.CMRA Iris.OFE
open scoped Iris

section Code

variable {E : Effect.{1}} [StateE RustHeap.{0} -< E] [StepE.{1} -< E]
variable [Aeneas.Std.FailE.{1} -< E]
variable [Aeneas.Std.ConcE.{1} -< E]
variable {T : Type}

noncomputable def new (x : T) : ITree E (Handle T) := do
  let s ← HeapAPI.alloc (1 : Int)
  let w ← HeapAPI.alloc (1 : Int)
  let d ← HeapAPI.alloc x
  return ⟨s, w, d⟩

noncomputable def deref (a : Handle T) : ITree E T :=
  HeapAPI.load a.data

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
    let _ ← free a.data
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
        let _ ← free a.strong
        free a.weak
      else
        return ()

/-- The retry is real here: the count may change between the load and the
compare-and-swap, so both are interference points. -/
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

section Specs

open AeneasIris.AtomicWpi
open AeneasIris.Heap AeneasIris.HeapAPI
open AeneasIris.ArcImpl

variable {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF] [HeapGS.{0} GF]
variable {E : Effect.{1}} [StateE RustHeap.{0} -< E] [StepE.{1} -< E]
variable [Aeneas.Std.FailE.{1} -< E]
variable [Aeneas.Std.ConcE.{1} -< E]
variable {Hd : Handler E GF} [stateH heapInterp -<ₕ Hd] [Conc.ConcH GF -<ₕ Hd]
variable {m : Mode} [stepH GF m -<ₕ Hd]
variable {T : Type} [ArcG GF T]

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


private theorem share_alloc (qs p : Qp) (m : Nat) (hv : (p + qs).val ≤ 1) :
    ((some (qs, PosNat.ofSucc m), (none : ArcShare)) : ArcShare × ArcShare)
      ~l~> ((some (p, 1) : ArcShare) • some (qs, PosNat.ofSucc m), some (p, 1)) :=
  LocalUpdate.op (fun _ _ => ⟨hv, trivial⟩)


private theorem share_dealloc (q : Qp) (zs : ArcShare) :
    (((some (q, 1) : ArcShare) • zs, (some (q, 1) : ArcShare)) : ArcShare × ArcShare)
      ~l~> (zs, none) :=
  LocalUpdate.cancel _ zs none


omit [HeapGS GF] in
private theorem keep_pure {P : IProp GF} {φ : Prop} (h : P ⊢ iprop(⌜φ⌝)) :
    P ⊢ iprop(⌜φ⌝ ∗ P) :=
  (BI.and_intro h .rfl).trans BI.persistent_and_sep_mp


omit [HeapGS GF] [StateE RustHeap -< E] [StepE -< E] [Aeneas.Std.FailE -< E] [Aeneas.Std.ConcE -< E] [stateH heapInterp -<ₕ Hd] [Conc.ConcH GF -<ₕ Hd] [stepH GF m -<ₕ Hd] in
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


omit [Conc.ConcH GF -<ₕ Hd] in
theorem new_spec (v : T) (M : CoPset) :
    ⦃ emp ⦄ (new (E := E) v) @ Hd ; m ; M
    ⦃ a, ∃ γ, arcAuth (T := T) γ 1 0 ∗ isArc γ a v ⦄ :=
  ArcImpl.new_spec v M

omit [Conc.ConcH GF -<ₕ Hd] in
theorem deref_spec (γ : GName) (a : Handle T) (v : T) (M : CoPset) :
    ⦃ isArc γ a v ⦄ (deref (E := E) a) @ Hd ; m ; M
    ⦃ r, ⌜r = v⌝ ∗ isArc γ a v ⦄ :=
  ArcImpl.deref_spec γ a v M

theorem strong_count_spec (γ : GName) (a : Handle T) (v : T) :
    ⊢ isArc γ a v -∗
      ⟪ ∀ n k, arcAuth (T := T) γ n k ⟫
        Hd m (strong_count (E := E) a) @ (∅ : CoPset)
      ⟪ arcAuth (T := T) γ n k | RET (n : Int); isArc γ a v ⟫ := by
  iintro HA
  simp only [atomicWpi]
  iintro %Φ HAU
  simp only [strong_count]
  simp only [AtomicHeapAPI.load]
  iapply Conc.wpi_sync
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
      ⟪ ∀ n k, arcAuth (T := T) γ n k ⟫
        Hd m (clone (E := E) a) @ (∅ : CoPset)
      ⟪ arcAuth (T := T) γ (n + 1) k | RET a; isArc γ a v ∗ isArc γ a v ⟫ := by
  iintro HA
  simp only [atomicWpi]
  iintro %Φ HAU
  simp only [clone]
  ibind
  simp only [AtomicHeapAPI.faa]
  iapply Conc.wpi_sync
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
      ⟪ ∀ n k, arcAuth (T := T) γ n k ⟫
        Hd m (downgrade (E := E) a) @ (∅ : CoPset)
      ⟪ arcAuth (T := T) γ n (k + 1)
      | w, RET w; isArc γ a v ∗ isWeak γ w v ⟫ := by
  iintro HA
  simp only [atomicWpi]
  iintro %Φ HAU
  simp only [downgrade]
  ibind
  simp only [AtomicHeapAPI.faa]
  iapply Conc.wpi_sync
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
      ⟪ ∀ n k, arcAuth (T := T) γ n k ⟫
        Hd m (drop_strong (E := E) a) @ (∅ : CoPset)
      ⟪ arcAuth (T := T) γ (n - 1) (if n = 1 then k + 1 else k)
      | w, RET (decide (n = 1)); if n = 1 then isWeak γ w v else emp ⟫ := by
  iintro HA
  simp only [atomicWpi]
  iintro %Φ HAU
  simp only [drop_strong]
  ibind
  simp only [AtomicHeapAPI.faa]
  iapply Conc.wpi_sync
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
        simp only [AtomicHeapAPI.free]
        iapply Conc.wpi_sync
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
      ⟪ arcAuth (T := T) γ n (k + 1) | RET w; isWeak γ w v ∗ isWeak γ w v ⟫ := by
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
    simp only [AtomicHeapAPI.faa]
    iapply Conc.wpi_sync
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


/-- Partial, as in `ArcAPI`: a thread that keeps losing the compare-and-swap
owes nothing.  Here the race it loses is one the model actually admits. -/
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
    simp only [AtomicHeapAPI.load]
    iapply Conc.wpi_sync
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
          simp only [AtomicHeapAPI.cas]
          iapply Conc.wpi_sync
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
    simp only [AtomicHeapAPI.load]
    iapply Conc.wpi_sync
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
    simp only [AtomicHeapAPI.faa]
    iapply Conc.wpi_sync
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
          simp only [AtomicHeapAPI.free]
          iapply Conc.wpi_sync
          iapply (HeapAPI.wpi_free (Hd := Hd) (m := m) (E := E) a'.strong ((0 : Nat) : Int))
          iapply (AeneasIris.Step.lat_intro m _)
          isplitl [Hs]
          · iexact Hs
          · imodintro
            iapply Conc.wpi_sync
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


omit [HeapGS GF] [stateH heapInterp -<ₕ Hd] [Conc.ConcH GF -<ₕ Hd] [stepH GF m -<ₕ Hd] [ArcG GF T] in
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

omit [HeapGS GF] [stateH heapInterp -<ₕ Hd] [Conc.ConcH GF -<ₕ Hd] [stepH GF m -<ₕ Hd] [ArcG GF T] in
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

omit [HeapGS GF] [stateH heapInterp -<ₕ Hd] [Conc.ConcH GF -<ₕ Hd] [stepH GF m -<ₕ Hd] [ArcG GF T] in
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

omit [HeapGS GF] [stateH heapInterp -<ₕ Hd] [Conc.ConcH GF -<ₕ Hd] [stepH GF m -<ₕ Hd] [ArcG GF T] in
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

/-- The interface is met over the atomic heap as well.

A `def` and not an `instance`: `ArcImpl` already supplies one at the same
`GF`, `Hd` and `m`, and search would have no way to choose.  A client that
wants the counts to be interference points names this one. -/
@[reducible] noncomputable def atomicArcAPI [stepH GF Mode.part -<ₕ Hd] :
    ArcAPI GF Hd m T where
  Arc := Handle
  Weak := WeakHandle

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

end AeneasIris.AtomicArcImpl
