import AeneasIris.Wpi
import Iris.Instances.Lib.Invariants

/-! # Structural rules for `wpi` -/

namespace AeneasIris

open Iris BI Aeneas.Data.Coinductive

section Rules

universe u v w

variable {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]
variable {E : Effect.{u}} {α : Type v} {β : Type w} {H : Handler E GF} {m : Mode}

/-- Once `False` is available, any mask can be produced: `False` entails the closing update itself. -/
theorem fupd_False_mask {E₁ E₂ E₃ : CoPset} :
    (iprop(|={E₁, E₂}=> False) : IProp GF) ⊢ iprop(|={E₁, E₃}=> False) :=
  .trans (BIFUpdate.mono BI.false_elim) BIFUpdate.trans

/-! ## Unfolding -/

/-- `wpi_unfold_emp_mask`. -/
theorem wpi_unfold_emp (t : ITree E α) (Φ : Post GF α) :
    wpi GF H m t Φ ⊣⊢ wpiAcc GF H m (fun p => wpi GF H m p.1.car p.2) (⟨t⟩, Φ) :=
  ⟨Iris.least_fixpoint_unfold_mp _, Iris.least_fixpoint_unfold_mpr _⟩

/-- `wpi_unfold`, the masked form. -/
theorem wpi_unfold (t : ITree E α) (Φ : Post GF α) (M : CoPset) :
    wpi_mask GF H m t Φ M ⊣⊢
      iprop(|={M, ∅}=> wpiAcc GF H m
        (fun p => wpi GF H m p.1.car p.2) (⟨t⟩, fun v => iprop(|={∅, M}=> Φ v))) := by
  simp only [wpi_mask]
  exact ⟨BIFUpdate.mono (wpi_unfold_emp t _).mp,
         BIFUpdate.mono (wpi_unfold_emp t _).mpr⟩

/-! ## Stepping rules -/

/-- `wpi_ret_emp_mask'`. -/
theorem wpi_ret_emp' (v : α) (Φ : Post GF α) :
    iprop(|={∅}=> Φ v) ⊣⊢ wpi GF H m (ITree.ret v) Φ := by
  refine .trans ?_ (wpi_unfold_emp _ _).symm
  simp only [wpiAcc, unfold_ret]
  exact .rfl

/-- `wpi_ret_emp_mask`. -/
theorem wpi_ret_emp (v : α) (Φ : Post GF α) : Φ v ⊢ wpi GF H m (ITree.ret v) Φ :=
  .trans Iris.fupd_intro (wpi_ret_emp' v Φ).mp

/-- `wpi_ret'`. -/
theorem wpi_ret' (v : α) (Φ : Post GF α) (M : CoPset) :
    iprop(|={M}=> Φ v) ⊣⊢ wpi_mask GF H m (ITree.ret v) Φ M := by
  simp only [wpi_mask]
  constructor
  · refine .trans (Iris.fupd_mask_intro_subseteq (E1 := M) (E2 := ∅) Iris.Std.LawfulSet.empty_subset) ?_
    refine BIFUpdate.mono (.trans ?_ (wpi_ret_emp' (H := H) v _).mp)
    exact .trans BIFUpdate.trans Iris.fupd_intro
  · refine .trans (BIFUpdate.mono (wpi_ret_emp' (H := H) v _).mpr) ?_
    exact .trans (BIFUpdate.mono BIFUpdate.trans) BIFUpdate.trans

/-- `wpi_ret`. -/
theorem wpi_ret (v : α) (Φ : Post GF α) (M : CoPset) :
    Φ v ⊢ wpi_mask GF H m (ITree.ret v) Φ M :=
  .trans Iris.fupd_intro (wpi_ret' v Φ M).mp

/-- A diverging tree satisfies no postcondition. -/
theorem wpi_div_emp (Φ : Post GF α) :
    wpi GF H m ITree.div Φ ⊣⊢ iprop(|={∅}=> divOK GF m) := by
  refine .trans (wpi_unfold_emp _ _) ?_
  simp only [wpiAcc, unfold_tau]
  exact .rfl

/-- `wpi_vis_emp_mask'`. -/
theorem wpi_vis_emp' (e : E.I) (k : E.O e → ITree E α) (Φ : Post GF α) :
    iprop(|={∅}=> H.run e (fun a => wpi GF H m (k a) Φ)
                          (fun a => iprop(|={⊤, ∅}=> wpi GF H m (k a) (fun _ => iprop(False)))))
      ⊣⊢ wpi GF H m (ITree.vis e k) Φ := by
  refine .trans ?_ (wpi_unfold_emp _ _).symm
  simp only [wpiAcc, unfold_vis]
  exact .rfl

/-- `wpi_vis_emp_mask`. -/
theorem wpi_vis_emp (e : E.I) (k : E.O e → ITree E α) (Φ : Post GF α) :
    H.run e (fun a => wpi GF H m (k a) Φ)
            (fun a => iprop(|={⊤, ∅}=> wpi GF H m (k a) (fun _ => iprop(False))))
      ⊢ wpi GF H m (ITree.vis e k) Φ :=
  .trans Iris.fupd_intro (wpi_vis_emp' e k Φ).mp

/-! ## Induction principles -/

/-- `wpi_ind_emp_mask`. -/
theorem wpi_ind_emp (G : ITree E α → Post GF α → IProp GF)
    (hne : ∀ t, OFE.NonExpansive (G t)) :
    iprop(□ ∀ t Φ,
      wpiAcc GF H m (fun p => iprop(G p.1.car p.2 ∧ wpi GF H m p.1.car p.2)) (⟨t⟩, Φ) -∗ G t Φ)
    ⊢ iprop(∀ t Φ, wpi GF H m t Φ -∗ G t Φ) := by
  letI : OFE.NonExpansive (fun p : WpIdx GF E α => G p.1.car p.2) := by
    constructor
    intro n p q hpq
    obtain ⟨ht, hΦ⟩ := hpq
    have hfst : p.fst = q.fst :=
      OFE.eq_of_eqv (OFE.discrete_0 (OFE.Dist.le ht (Nat.zero_le n)))
    rw [hfst]
    exact (hne _).ne hΦ
  simp only [wpi]
  iintro #Hpre %t %Φ Hwp
  iapply (Iris.least_fixpoint_ind (F := wpiAcc GF H m)
            (Φ := fun p : WpIdx GF E α => G p.1.car p.2)) $$ [] %(⟨t⟩, Φ) Hwp
  iintro !> %p HF
  iapply Hpre $$ HF

/-- `wpi_iter_emp_mask`. -/
theorem wpi_iter_emp (G : ITree E α → Post GF α → IProp GF)
    (hne : ∀ t, OFE.NonExpansive (G t)) :
    iprop(□ ∀ t Φ, wpiAcc GF H m (fun p => G p.1.car p.2) (⟨t⟩, Φ) -∗ G t Φ)
    ⊢ iprop(∀ t Φ, wpi GF H m t Φ -∗ G t Φ) := by
  letI : OFE.NonExpansive (fun p : WpIdx GF E α => G p.1.car p.2) := by
    constructor
    intro n p q hpq
    obtain ⟨ht, hΦ⟩ := hpq
    have hfst : p.fst = q.fst :=
      OFE.eq_of_eqv (OFE.discrete_0 (OFE.Dist.le ht (Nat.zero_le n)))
    rw [hfst]
    exact (hne _).ne hΦ
  simp only [wpi]
  iintro #Hpre %t %Φ Hwp
  iapply (Iris.least_fixpoint_iter (F := wpiAcc GF H m)
            (Φ := fun p : WpIdx GF E α => G p.1.car p.2)) $$ [] %(⟨t⟩, Φ) Hwp
  iintro !> %p HF
  iapply Hpre $$ HF

/-- `wpi_iter_emp_mask'`: the iterator with one hypothesis *per constructor*. -/
theorem wpi_iter_emp' (G : ITree E α → Post GF α → IProp GF)
    (hne : ∀ t, OFE.NonExpansive (G t)) :
    ⊢ iprop(
      □ (∀ (Φ : Post GF α) (v : α), (|={∅}=> Φ v) -∗ G (ITree.ret v) Φ) -∗
      □ (∀ (Φ : Post GF α),
          (|={∅}=> divOK GF m) -∗ G ITree.div Φ) -∗
      □ (∀ (Φ : Post GF α) (e : E.I) (k : E.O e → ITree E α),
          (|={∅}=> H.run e (fun a => G (k a) Φ)
                           (fun a => iprop(|={⊤, ∅}=> G (k a) (fun _ => iprop(False)))))
          -∗ G (ITree.vis e k) Φ) -∗
      ∀ t Φ, wpi GF H m t Φ -∗ G t Φ) := by
  iintro #HRet #HDiv #HVis
  iapply (wpi_iter_emp (H := H) G hne)
  iintro !> %t %Φ
  induction t using ITree.cases
  · rename_i r
    simp only [wpiAcc, show (Pure.pure r : ITree E α) = ITree.ret r from rfl, unfold_ret]
    iintro HF
    iapply HRet $$ %Φ %r HF
  · simp only [wpiAcc, unfold_tau]
    iintro HF
    iapply HDiv $$ %Φ HF
  · rename_i e k
    simp only [wpiAcc, unfold_vis]
    iintro HF
    iapply HVis $$ %Φ %e %k HF

/-! ## Ghost updates -/

/-- `wpi_update_emp_mask`. -/
theorem wpi_update_emp (t : ITree E α) (Φ : Post GF α) :
    iprop(|={∅}=> wpi GF H m t Φ) ⊣⊢ wpi GF H m t Φ := by
  constructor
  ·
    refine .trans (BIFUpdate.mono (wpi_unfold_emp t Φ).mp) ?_
    refine .trans ?_ (wpi_unfold_emp t Φ).mpr
    simp only [wpiAcc]
    exact BIFUpdate.trans
  · exact Iris.fupd_intro

/-- `wpi_update`. -/
theorem wpi_update (t : ITree E α) (Φ : Post GF α) (M : CoPset) :
    iprop(|={M}=> wpi_mask GF H m t Φ M) ⊣⊢ wpi_mask GF H m t Φ M := by
  constructor
  · simp only [wpi_mask]; exact BIFUpdate.trans
  · exact Iris.fupd_intro

/-! ## Consequence -/

/-- `wpi_upd_wand_emp_mask`: the strongest consequence rule, weakening under an update. -/
theorem wpi_upd_wand_emp (t : ITree E α) (Φ Ψ : Post GF α) :
    iprop(∀ v, (|={∅}=> Φ v) -∗ (|={∅}=> Ψ v)) ⊢ iprop(wpi GF H m t Φ -∗ wpi GF H m t Ψ) := by
  iintro Hwand Hwp
  ihave Hgen :
      iprop(∀ (t' : ITree E α) (Φ' : Post GF α),
        wpi GF H m t' Φ' -∗
        ∀ Ψ' : Post GF α, (∀ v, (|={∅}=> Φ' v) -∗ (|={∅}=> Ψ' v)) -∗ wpi GF H m t' Ψ') $$ []
  · iapply (wpi_iter_emp' (H := H)
      (G := fun t' Φ' => iprop(∀ Ψ' : Post GF α,
        (∀ v, (|={∅}=> Φ' v) -∗ (|={∅}=> Ψ' v)) -∗ wpi GF H m t' Ψ')))
    · intro t'
      constructor
      intro n Φ₁ Φ₂ hΦ
      refine BI.forall_ne fun Ψ' => BI.wand_ne.ne ?_ .rfl
      exact BI.forall_ne fun v => BI.wand_ne.ne (BIFUpdate.ne.ne (hΦ v)) .rfl
    ·
      iintro !> %Φ' %v HΦ %Ψ' Hw
      iapply (wpi_ret_emp' (H := H) v Ψ').mp
      iapply Hw $$ HΦ
    ·
      iintro !> %Φ' HF %Ψ' _
      iapply (wpi_div_emp (H := H) Ψ').mpr
      iexact HF
    ·
      iintro !> %Φ' %e %k HF %Ψ' Hw
      iapply (wpi_vis_emp' (H := H) e k Ψ').mp
      imod HF with HF
      imodintro
      iapply H.mono e $$ [Hw] [] HF
      · iintro %a HG
        iapply HG $$ %Ψ' Hw
      · iintro !> %a HG
        imod HG with HG
        imodintro
        iapply HG $$ %(fun _ => iprop(False))
        iintro %v HF
        imod HF with HF
        iexfalso
        iexact HF
  · iapply Hgen $$ %t %Φ Hwp Hwand

/-- `wpi_wand_emp_mask`. -/
theorem wpi_wand_emp (t : ITree E α) (Φ Ψ : Post GF α) :
    iprop(∀ v, Φ v -∗ Ψ v) ⊢ iprop(wpi GF H m t Φ -∗ wpi GF H m t Ψ) := by
  iintro Hw
  iapply wpi_upd_wand_emp
  iintro %v HΦ
  imod HΦ with HΦ
  imodintro
  iapply Hw $$ HΦ

/-- Pointwise monotonicity: the form of the consequence rule that is convenient -/
theorem wpi_mono_emp {Φ Ψ : Post GF α} (t : ITree E α) (h : ∀ v, Φ v ⊢ Ψ v) :
    wpi GF H m t Φ ⊢ wpi GF H m t Ψ := by
  iintro Hwp
  iapply wpi_wand_emp $$ [] Hwp
  iintro %v
  iapply BI.entails_wand (h v)

/-- `wpi_wand`. -/
theorem wpi_wand (t : ITree E α) (Φ Ψ : Post GF α) (M : CoPset) :
    iprop(∀ v, Φ v -∗ Ψ v) ⊢ iprop(wpi_mask GF H m t Φ M -∗ wpi_mask GF H m t Ψ M) := by
  simp only [wpi_mask]
  iintro Hw Hwp
  imod Hwp with Hwp
  imodintro
  iapply wpi_wand_emp $$ [Hw] Hwp
  iintro %v HΦ
  imod HΦ with HΦ
  imodintro
  iapply Hw $$ HΦ

/-- `wpi_update_post_emp_mask`. -/
theorem wpi_update_post_emp (t : ITree E α) (Φ : Post GF α) :
    wpi GF H m t (fun v => iprop(|={∅}=> Φ v)) ⊣⊢ wpi GF H m t Φ := by
  constructor
  · iintro Hwp
    iapply wpi_upd_wand_emp $$ [] Hwp
    iintro %v HΦ
    imod HΦ with HΦ
    iexact HΦ
  · iintro Hwp
    iapply wpi_upd_wand_emp $$ [] Hwp
    iintro %v HΦ
    imod HΦ with HΦ
    imodintro
    imodintro
    iexact HΦ

/-- `wpi_update_post`. -/
theorem wpi_update_post (t : ITree E α) (Φ : Post GF α) (M : CoPset) :
    wpi_mask GF H m t (fun v => iprop(|={M}=> Φ v)) M ⊣⊢ wpi_mask GF H m t Φ M := by
  simp only [wpi_mask]
  constructor
  · iintro Hwp
    imod Hwp with Hwp
    imodintro
    iapply wpi_wand_emp $$ [] Hwp
    iintro %v HΦ
    imod HΦ with HΦ
    imod HΦ with HΦ
    imodintro
    iexact HΦ
  · iintro Hwp
    imod Hwp with Hwp
    imodintro
    iapply wpi_wand_emp $$ [] Hwp
    iintro %v HΦ
    imod HΦ with HΦ
    imodintro
    imodintro
    iexact HΦ

/-! ## Handler refinement -/

/-- `wpi_wandH_emp_mask`. -/
theorem wpi_wandH_emp {H₁ H₂ : Handler E GF} {m₁ m₂ : Mode}
    [W : wandH H₁ H₂]
    (hdiv : divOK GF m₁ ⊢ divOK GF m₂)
    (t : ITree E α) (Φ : Post GF α) :
    wpi GF H₁ m₁ t Φ ⊢ wpi GF H₂ m₂ t Φ := by
  ihave Hgen : iprop(∀ (t' : ITree E α) (Φ' : Post GF α),
      wpi GF H₁ m₁ t' Φ' -∗ wpi GF H₂ m₂ t' Φ') $$ []
  · iapply (wpi_iter_emp' (H := H₁) (G := fun t' Φ' => wpi GF H₂ m₂ t' Φ'))
    ·
      intro t'
      constructor
      intro n Φ₁ Φ₂ hΦ
      simp only [wpi]
      exact OFE.NonExpansive.ne (f := bi_least_fixpoint (wpiAcc GF H₂ m₂)) ⟨.rfl, hΦ⟩
    ·
      iintro !> %Φ' %v HΦ
      iapply (wpi_ret_emp' (H := H₂) v Φ').mp
      iexact HΦ
    ·
      iintro !> %Φ' HF
      iapply (wpi_div_emp (H := H₂) Φ').mpr
      imod HF with HF
      imodintro
      iapply (BI.entails_wand hdiv)
      iexact HF
    ·
      iintro !> %Φ' %e %k HH
      iapply (wpi_vis_emp' (H := H₂) e k Φ').mp
      imod HH with HH
      imodintro
      iapply W.is_wandH e
      iexact HH
  iintro Hwp
  iapply Hgen $$ %t %Φ Hwp

/-- `wpi_wandH`. -/
theorem wpi_wandH {H₁ H₂ : Handler E GF} {m₁ m₂ : Mode}
    [wandH H₁ H₂]
    (hdiv : divOK GF m₁ ⊢ divOK GF m₂)
    (t : ITree E α) (Φ : Post GF α) (M : CoPset) :
    wpi_mask GF H₁ m₁ t Φ M ⊢ wpi_mask GF H₂ m₂ t Φ M := by
  simp only [wpi_mask]
  exact BIFUpdate.mono (wpi_wandH_emp hdiv t _)

/-! ## Masked stepping rules for `vis` -/

/-- `wpi_vis'`. -/
theorem wpi_vis' (e : E.I) (k : E.O e → ITree E α) (Φ : Post GF α) (M : CoPset) :
    iprop(|={M, ∅}=> H.run e
        (fun a => wpi_mask GF H m (k a) (fun v => iprop(|={∅, M}=> Φ v)) ∅)
        (fun a => wpi_mask GF H m (k a) (fun _ => iprop(False)) ⊤))
      ⊣⊢ wpi_mask GF H m (ITree.vis e k) Φ M := by
  simp only [wpi_mask]
  constructor
  ·
    refine BIFUpdate.mono
      (.trans ?_ (.trans Iris.fupd_intro (wpi_vis_emp' (H := H) e k _).mp))
    iintro HH
    iapply H.mono e $$ [] [] HH
    ·
      iintro %a Hwp
      iapply (wpi_update_emp (H := H) (k a) _).mp
      imod Hwp with Hwp
      imodintro
      iapply (wpi_update_post_emp (H := H) (k a) _).mp $$ Hwp
    ·
      iintro !> %a Hwp
      imod Hwp with Hwp
      imodintro
      iapply (wpi_update_post_emp (H := H) (k a) _).mp
      iapply wpi_wand_emp $$ [] Hwp
      iintro %v Hf
      iapply fupd_False_mask
      iexact Hf
  · refine .trans (BIFUpdate.mono (wpi_vis_emp' (H := H) e k _).mpr) ?_
    refine .trans BIFUpdate.trans (BIFUpdate.mono ?_)
    iintro HH
    iapply H.mono e $$ [] [] HH
    · iintro %a Hwp
      imodintro
      iapply (wpi_update_post_emp (H := H) (k a) _).mpr $$ Hwp
    · iintro !> %a Hwp
      imod Hwp with Hwp
      imodintro
      iapply wpi_wand_emp $$ [] Hwp
      iintro %v Hf
      iexfalso
      iexact Hf

/-- `wpi_vis`. -/
theorem wpi_vis (e : E.I) (k : E.O e → ITree E α) (Φ : Post GF α) (M : CoPset) :
    iprop(|={M, ∅}=> H.run e
        (fun a => wpi_mask GF H m (k a) (fun v => iprop(|={∅, M}=> Φ v)) ∅)
        (fun a => wpi_mask GF H m (k a) (fun _ => iprop(False)) ⊤))
      ⊢ wpi_mask GF H m (ITree.vis e k) Φ M :=
  (wpi_vis' e k Φ M).mp

/-- `wpi_trigger`: the rule an effect library actually uses. -/
theorem wpi_trigger {E' : Effect} [Sub : E' -< E] (e : E'.I) (Φ : Post GF (E'.O e))
    (M : CoPset) (H' : Handler E' GF)
    (hrun : ∀ (Ψ B : E'.O e → IProp GF),
      H'.run e Ψ B ⊢ H.run (Subeffect.map (E₁ := E') e).1
        (fun x => Ψ ((Subeffect.map (E₁ := E') e).2 x))
        (fun x => B ((Subeffect.map (E₁ := E') e).2 x))) :
    iprop(|={M, ∅}=> H'.run e (fun a => iprop(|={∅, M}=> Φ a)) (fun _ => iprop(False)))
      ⊢ wpi_mask GF H m (Effect.trigger E' e) Φ M := by
  simp only [Effect.trigger]
  refine .trans ?_ (wpi_vis (H := H) _ _ Φ M)
  refine BIFUpdate.mono (.trans (hrun _ _) ?_)
  iintro HH
  iapply H.mono _ $$ [] [] HH
  · iintro %a HΦ
    iapply (wpi_ret' (H := H) _ (fun v => iprop(|={∅, M}=> Φ v)) ∅).mp
    imodintro
    iexact HΦ
  · iintro !> %a Hf
    iexfalso
    iexact Hf

/-- `wpi_trigger`, with the side condition discharged by instance search rather than passed by hand. -/
theorem wpi_trigger' {E' : Effect} [E' -< E] {H' : Handler E' GF} [inH H' H]
    (e : E'.I) (Φ : Post GF (E'.O e)) (M : CoPset) :
    iprop(|={M, ∅}=> H'.run e (fun a => iprop(|={∅, M}=> Φ a)) (fun _ => iprop(False)))
      ⊢ wpi_mask GF H m (Effect.trigger E' e) Φ M :=
  wpi_trigger e Φ M H' (inH.embed e)

/-! ## Sequencing -/

/-- `wpi_bind_emp_mask`. -/
theorem wpi_bind_emp (t : ITree E α) (k : α → ITree E β) (Φ : Post GF β) :
    wpi GF H m t (fun v => wpi GF H m (k v) Φ) ⊢ wpi GF H m (ITree.bind t k) Φ := by
  iintro Hwp
  ihave Hgen :
      iprop(∀ (t' : ITree E α) (Φ' : Post GF α),
        wpi GF H m t' Φ' -∗
        ∀ (Ψ : Post GF β) (k' : α → ITree E β),
          (∀ v, Φ' v -∗ wpi GF H m (k' v) Ψ) -∗ wpi GF H m (ITree.bind t' k') Ψ) $$ []
  · iapply (wpi_iter_emp' (H := H)
      (G := fun t' Φ' => iprop(∀ (Ψ : Post GF β) (k' : α → ITree E β),
        (∀ v, Φ' v -∗ wpi GF H m (k' v) Ψ) -∗ wpi GF H m (ITree.bind t' k') Ψ)))
    · intro t'
      constructor
      intro n Φ₁ Φ₂ hΦ
      refine BI.forall_ne fun Ψ => BI.forall_ne fun k' => BI.wand_ne.ne ?_ .rfl
      exact BI.forall_ne fun v => BI.wand_ne.ne (hΦ v) .rfl
    ·
      iintro !> %Φ' %v HΦ %Ψ %k' Hw
      simp only [itree_ret_bind]
      iapply (wpi_update_emp (H := H) (k' v) Ψ).mp
      imod HΦ with HΦ
      imodintro
      iapply Hw $$ HΦ
    ·
      iintro !> %Φ' HF %Ψ %k' _
      simp only [itree_div_bind]
      iapply (wpi_div_emp (H := H) Ψ).mpr
      iexact HF
    ·
      iintro !> %Φ' %e %k HF %Ψ %k' Hw
      simp only [itree_vis_bind]
      iapply (wpi_vis_emp' (H := H) e (fun o => ITree.bind (k o) k') Ψ).mp
      imod HF with HF
      imodintro
      iapply H.mono e $$ [Hw] [] HF
      · iintro %a HG
        iapply HG $$ %Ψ %k' Hw
      · iintro !> %a HG
        imod HG with HG
        imodintro
        iapply HG $$ %(fun _ => iprop(False)) %k'
        iintro %v HF
        iexfalso
        iexact HF
  ·
    iapply Hgen $$ %t %(fun v => wpi GF H m (k v) Φ) Hwp %Φ %k
    iintro %v HΦ
    iexact HΦ

/-- `wpi_bind`. -/
theorem wpi_bind (t : ITree E α) (k : α → ITree E β) (Φ : Post GF β) (M : CoPset) :
    wpi_mask GF H m t (fun v => wpi_mask GF H m (k v) Φ M) M
      ⊢ wpi_mask GF H m (ITree.bind t k) Φ M := by
  simp only [wpi_mask]
  refine BIFUpdate.mono (.trans ?_ (wpi_bind_emp (H := H) t k _))
  exact wpi_mono_emp t fun v =>
    .trans BIFUpdate.trans (wpi_update_emp (H := H) (k v) _).mp

/-! ## Framing -/

/-- `wpi_frame_l_emp_mask`. -/
theorem wpi_frame_l_emp (t : ITree E α) (Φ : Post GF α) (P : IProp GF) :
    iprop(P ∗ wpi GF H m t Φ) ⊢ wpi GF H m t (fun v => iprop(P ∗ Φ v)) := by
  iintro ⟨HP, Hwp⟩
  iapply wpi_wand_emp $$ [HP] Hwp
  iintro %v HΦ
  isplitl [HP]
  · iexact HP
  · iexact HΦ

/-- `wpi_frame_r_emp_mask`. -/
theorem wpi_frame_r_emp (t : ITree E α) (Φ : Post GF α) (P : IProp GF) :
    iprop(wpi GF H m t Φ ∗ P) ⊢ wpi GF H m t (fun v => iprop(Φ v ∗ P)) := by
  iintro ⟨Hwp, HP⟩
  iapply wpi_wand_emp $$ [HP] Hwp
  iintro %v HΦ
  isplitl [HΦ]
  · iexact HΦ
  · iexact HP

/-- `wpi_frame_l`. -/
theorem wpi_frame_l (t : ITree E α) (Φ : Post GF α) (P : IProp GF) (M : CoPset) :
    iprop(P ∗ wpi_mask GF H m t Φ M) ⊢ wpi_mask GF H m t (fun v => iprop(P ∗ Φ v)) M := by
  iintro ⟨HP, Hwp⟩
  iapply wpi_wand $$ [HP] Hwp
  iintro %v HΦ
  isplitl [HP]
  · iexact HP
  · iexact HΦ

/-- `wpi_frame_r`. -/
theorem wpi_frame_r (t : ITree E α) (Φ : Post GF α) (P : IProp GF) (M : CoPset) :
    iprop(wpi_mask GF H m t Φ M ∗ P) ⊢ wpi_mask GF H m t (fun v => iprop(Φ v ∗ P)) M := by
  iintro ⟨Hwp, HP⟩
  iapply wpi_wand $$ [HP] Hwp
  iintro %v HΦ
  isplitl [HΦ]
  · iexact HΦ
  · iexact HP

/-! ## Masks -/

/-- `wpi_reduce_mask`. -/
theorem wpi_reduce_mask (t : ITree E α) (Φ : Post GF α) (M M' : CoPset) :
    iprop(|={M, M'}=> wpi_mask GF H m t (fun v => iprop(|={M', M}=> Φ v)) M')
      ⊢ wpi_mask GF H m t Φ M := by
  simp only [wpi_mask]
  iintro Hwp
  imod Hwp with Hwp
  imod Hwp with Hwp
  imodintro
  iapply wpi_wand_emp $$ [] Hwp
  iintro %v HΦ
  imod HΦ with HΦ
  imod HΦ with HΦ
  imodintro
  iexact HΦ

/-- `wpi_clear_mask`. -/
theorem wpi_clear_mask (t : ITree E α) (Φ : Post GF α) (M : CoPset) :
    iprop(|={M, ∅}=> wpi_mask GF H m t (fun v => iprop(|={∅, M}=> Φ v)) ∅)
      ⊣⊢ wpi_mask GF H m t Φ M := by
  simp only [wpi_mask]
  constructor
  · iintro Hwp
    imod Hwp with Hwp
    imod Hwp with Hwp
    imodintro
    iapply wpi_wand_emp $$ [] Hwp
    iintro %v HΦ
    imod HΦ with HΦ
    imod HΦ with HΦ
    imodintro
    iexact HΦ
  ·
    exact BIFUpdate.mono
      (((wpi_update_post_emp (H := H) t _).mpr).trans Iris.fupd_intro)

/-- `wpi_mask_mono`. -/
theorem wpi_mask_mono (t : ITree E α) (Φ : Post GF α) (M M' : CoPset)
    (hsub : M ⊆ M') :
    wpi_mask GF H m t Φ M ⊢ wpi_mask GF H m t Φ M' := by
  iintro Hwp
  iapply (wpi_reduce_mask (H := H) t Φ M' M)
  iapply (Iris.fupd_mask_intro (E1 := M') (E2 := M) hsub)
  iintro Hclose
  iapply wpi_wand $$ [Hclose] Hwp
  iintro %v HΦ
  imod Hclose with _
  imodintro
  iexact HΦ

/-! ## Invariants -/

/-- `wpi_open_invariant`. -/
theorem wpi_open_invariant (N : Namespace) (M : CoPset)
    (t : ITree E α) (Φ : Post GF α) (P : IProp GF) (hsub : (↑N : CoPset) ⊆ M) :
    ⊢ iprop(Iris.inv N P -∗
        (▷ P -∗ wpi_mask GF H m t (fun v => iprop(▷ P ∗ Φ v)) (SDiff.sdiff M (↑N : CoPset))) -∗
        wpi_mask GF H m t Φ M) := by
  iintro HI Hwp
  iapply (wpi_reduce_mask (H := H) t Φ M (SDiff.sdiff M (↑N : CoPset)))
  ihave Hacc := Iris.inv_acc (P := P) hsub $$ HI
  imod Hacc with ⟨HP, Hclose⟩
  imodintro
  ispecialize Hwp $$ HP
  iapply wpi_wand $$ [Hclose] Hwp
  iintro %v ⟨HP, HΦ⟩
  imod Hclose $$ HP with _
  imodintro
  iexact HΦ

/-- `wpi_open_invariant_timeless`. -/
theorem wpi_open_invariant_timeless (N : Namespace)
    (M : CoPset) (t : ITree E α) (Φ : Post GF α) (P : IProp GF) [BI.Timeless P]
    (hsub : (↑N : CoPset) ⊆ M) :
    ⊢ iprop(Iris.inv N P -∗
        (P -∗ wpi_mask GF H m t (fun v => iprop(P ∗ Φ v)) (SDiff.sdiff M (↑N : CoPset))) -∗
        wpi_mask GF H m t Φ M) := by
  letI : Iris.ProofMode.IsExcept0 (wpi_mask GF H m t (fun v => iprop(P ∗ Φ v))
      (SDiff.sdiff M (↑N : CoPset))) := by
    simp only [wpi_mask]; infer_instance
  iintro HI Hwp
  iapply (wpi_open_invariant (H := H) N M t Φ P hsub) $$ HI
  iintro HP
  iapply (wpi_wand (H := H) t (fun v => iprop(P ∗ Φ v)) (fun v => iprop(▷ P ∗ Φ v)) _) $$ []
  · iintro %v ⟨HP, HΦ⟩
    isplitl [HP]
    · inext
      iexact HP
    · iexact HΦ
  · imod HP with HP
    iapply Hwp $$ HP

/-! ## The `step` event -/

end Rules

end AeneasIris
