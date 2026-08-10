import AeneasIris.wpi
import Iris.Instances.Lib.Invariants

/-!
# Structural rules for `wpi`

Statements ported from `src/wpi.v` of the "Program Logics à la Carte" artifact
(Vistrup, Sammler, Jung). Proofs are deferred: this file fixes the *interface*
first, as agreed, so that the effect libraries and the tactic layer can be built
against a stable set of rules.

## Layering

The Coq development states every rule twice: once at the empty mask (suffix
`_emp_mask`, working directly on the least fixpoint) and once at a general mask
(no suffix, working on `wpi_mask`). We keep that split, because the empty-mask
versions are what the fixpoint induction principles actually operate on, and the
masked ones are what clients use.

## Differences from the Coq development

* **No `tau`.** Our `ITreeF` is `ret | div | vis`; silent divergence is the
  bottom element `div` rather than an infinite `tau` chain. So `wpi_tau` and
  `wpi_tau_emp_mask` have no counterpart, and there is instead a rule for `div`.
* **`div ⇒ False`.** `wpiAcc` sends `div` to `False`, so `wpi` is
  termination-*sensitive* by default, exactly as in the paper. Termination-
  insensitive reasoning is bought with the `StepE` menu item (see
  `AeneasIris.Step`), not by weakening `wpi`.
* **Deferred.** `wpi_translation*`, `wpi_inH*` and `wpi_wandH` — the rules for
  embedding one effect signature or handler into another — are not stated here.
  They are needed for modular composition of handlers, not for the first
  end-to-end proof.
-/

namespace AeneasIris

open Iris BI Aeneas.Data.Coinductive

section Rules

/- `u` is the effect's universe; `v` and `w` are return-type universes. All
three are kept separate: `wpi_bind` sequences a `Type v` computation into a
`Type w` one (e.g. reading a `Type u` state and returning `Unit`), so tying
`α` and `β` together would rule out exactly the compositions we need. -/
universe u v w

variable {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]
variable {E : Effect.{u}} {α : Type v} {β : Type w} {H : Handler E GF}

/-- Once `False` is available, any mask can be produced: `False` entails the
closing update itself. This is what lets a spawned thread's postcondition move
between masks, and it is the only mask manipulation the `vis` rules need. -/
theorem fupd_False_mask {E₁ E₂ E₃ : CoPset} :
    (iprop(|={E₁, E₂}=> False) : IProp GF) ⊢ iprop(|={E₁, E₃}=> False) :=
  .trans (BIFUpdate.mono BI.false_elim) BIFUpdate.trans

/-! ## Unfolding

`wpi` is a least fixpoint, so it satisfies its own defining equation. Everything
below is derived from this together with the induction principle. -/

/-- `wpi_unfold_emp_mask`. -/
theorem wpi_unfold_emp (t : ITree E α) (Φ : Post GF α) :
    wpi GF H t Φ ⊣⊢ wpiAcc GF H (fun p => wpi GF H p.1.car p.2) (⟨t⟩, Φ) :=
  ⟨Iris.least_fixpoint_unfold_mp _, Iris.least_fixpoint_unfold_mpr _⟩

/-- `wpi_unfold`, the masked form. Note the right-hand side mentions `wpi_mask`
at the *empty* mask: a node is where the mask is closed. -/
theorem wpi_unfold (t : ITree E α) (Φ : Post GF α) (M : CoPset) :
    wpi_mask GF H t Φ M ⊣⊢
      iprop(|={M, ∅}=> wpiAcc GF H
        (fun p => wpi GF H p.1.car p.2) (⟨t⟩, fun v => iprop(|={∅, M}=> Φ v))) := by
  simp only [wpi_mask]
  exact ⟨BIFUpdate.mono (wpi_unfold_emp t _).mp,
         BIFUpdate.mono (wpi_unfold_emp t _).mpr⟩

/-! ## Stepping rules

One per constructor of `ITreeF`. -/

/-- `wpi_ret_emp_mask'`. Note this is a biconditional: at the empty mask a
returning tree is *exactly* its postcondition, up to a ghost update. -/
theorem wpi_ret_emp' (v : α) (Φ : Post GF α) :
    iprop(|={∅}=> Φ v) ⊣⊢ wpi GF H (ITree.ret v) Φ := by
  refine .trans ?_ (wpi_unfold_emp _ _).symm
  simp only [wpiAcc, unfold_ret]
  exact .rfl

/-- `wpi_ret_emp_mask`. -/
theorem wpi_ret_emp (v : α) (Φ : Post GF α) : Φ v ⊢ wpi GF H (ITree.ret v) Φ :=
  .trans Iris.fupd_intro (wpi_ret_emp' v Φ).mp

/-- `wpi_ret'`. -/
theorem wpi_ret' (v : α) (Φ : Post GF α) (M : CoPset) :
    iprop(|={M}=> Φ v) ⊣⊢ wpi_mask GF H (ITree.ret v) Φ M := by
  simp only [wpi_mask]
  constructor
  · refine .trans (Iris.fupd_mask_intro_subseteq (E1 := M) (E2 := ∅) Iris.Std.LawfulSet.empty_subset) ?_
    refine BIFUpdate.mono (.trans ?_ (wpi_ret_emp' (H := H) v _).mp)
    exact .trans BIFUpdate.trans Iris.fupd_intro
  · refine .trans (BIFUpdate.mono (wpi_ret_emp' (H := H) v _).mpr) ?_
    exact .trans (BIFUpdate.mono BIFUpdate.trans) BIFUpdate.trans

/-- `wpi_ret`. -/
theorem wpi_ret (v : α) (Φ : Post GF α) (M : CoPset) :
    Φ v ⊢ wpi_mask GF H (ITree.ret v) Φ M :=
  .trans Iris.fupd_intro (wpi_ret' v Φ M).mp

/-- A diverging tree satisfies no postcondition. This is where termination
sensitivity lives: it has no counterpart in the Coq development, whose `ITree`
carries `tau` instead of a bottom element. To reason about non-terminating code,
insert `StepE` events and choose `stepH .later` (see `AeneasIris.Step`). -/
theorem wpi_div_emp (Φ : Post GF α) : wpi GF H ITree.div Φ ⊣⊢ iprop(|={∅}=> False) := by
  refine .trans (wpi_unfold_emp _ _) ?_
  simp only [wpiAcc, unfold_tau]
  exact .rfl

/-- `wpi_vis_emp_mask'`. The handler receives two continuations: the sequential
one, and the one a *spawning* handler would give to a new thread — the latter
under `|={⊤,∅}=>` with postcondition `False`, which `ConcE`'s `endthread`
discharges. -/
theorem wpi_vis_emp' (e : E.I) (k : E.O e → ITree E α) (Φ : Post GF α) :
    iprop(|={∅}=> H.run e (fun a => wpi GF H (k a) Φ)
                          (fun a => iprop(|={⊤, ∅}=> wpi GF H (k a) (fun _ => iprop(False)))))
      ⊣⊢ wpi GF H (ITree.vis e k) Φ := by
  refine .trans ?_ (wpi_unfold_emp _ _).symm
  simp only [wpiAcc, unfold_vis]
  exact .rfl

/-- `wpi_vis_emp_mask`. -/
theorem wpi_vis_emp (e : E.I) (k : E.O e → ITree E α) (Φ : Post GF α) :
    H.run e (fun a => wpi GF H (k a) Φ)
            (fun a => iprop(|={⊤, ∅}=> wpi GF H (k a) (fun _ => iprop(False))))
      ⊢ wpi GF H (ITree.vis e k) Φ :=
  .trans Iris.fupd_intro (wpi_vis_emp' e k Φ).mp

/-! ## Induction principles

These are the workhorses: `wpi_bind` and `wpi_wand` are both proved from
`wpi_iter_emp`, not from `wpi_unfold`. -/

/-- `wpi_ind_emp_mask`. The strong induction principle: the hypothesis may use
both the inductive hypothesis `G` *and* the original `wpi` at each recursive
occurrence. -/
theorem wpi_ind_emp (G : ITree E α → Post GF α → IProp GF)
    (hne : ∀ t, OFE.NonExpansive (G t)) :
    iprop(□ ∀ t Φ,
      wpiAcc GF H (fun p => iprop(G p.1.car p.2 ∧ wpi GF H p.1.car p.2)) (⟨t⟩, Φ) -∗ G t Φ)
    ⊢ iprop(∀ t Φ, wpi GF H t Φ -∗ G t Φ) := by
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
  iapply (Iris.least_fixpoint_ind (F := wpiAcc GF H)
            (Φ := fun p : WpIdx GF E α => G p.1.car p.2)) $$ [] %(⟨t⟩, Φ) Hwp
  iintro !> %p HF
  iapply Hpre $$ HF

/-- `wpi_iter_emp_mask`. The weaker, more convenient form: only the inductive
hypothesis is available. -/
theorem wpi_iter_emp (G : ITree E α → Post GF α → IProp GF)
    (hne : ∀ t, OFE.NonExpansive (G t)) :
    iprop(□ ∀ t Φ, wpiAcc GF H (fun p => G p.1.car p.2) (⟨t⟩, Φ) -∗ G t Φ)
    ⊢ iprop(∀ t Φ, wpi GF H t Φ -∗ G t Φ) := by
  /- `G` uncurried is the predicate `least_fixpoint_iter` expects. -/
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
  iapply (Iris.least_fixpoint_iter (F := wpiAcc GF H)
            (Φ := fun p : WpIdx GF E α => G p.1.car p.2)) $$ [] %(⟨t⟩, Φ) Hwp
  iintro !> %p HF
  iapply Hpre $$ HF

/-- `wpi_iter_emp_mask'`: the iterator with one hypothesis *per constructor*.

This is the form the Coq development actually uses to prove `wpi_upd_wand_emp`
and `wpi_bind_emp` (`wpi.v` lines 287 and 325): it performs the case analysis on
the node once and for all, so the client never has to unfold `wpiAcc`. -/
theorem wpi_iter_emp' (G : ITree E α → Post GF α → IProp GF)
    (hne : ∀ t, OFE.NonExpansive (G t)) :
    ⊢ iprop(
      □ (∀ (Φ : Post GF α) (v : α), (|={∅}=> Φ v) -∗ G (ITree.ret v) Φ) -∗
      □ (∀ (Φ : Post GF α), (|={∅}=> False) -∗ G ITree.div Φ) -∗
      □ (∀ (Φ : Post GF α) (e : E.I) (k : E.O e → ITree E α),
          (|={∅}=> H.run e (fun a => G (k a) Φ)
                           (fun a => iprop(|={⊤, ∅}=> G (k a) (fun _ => iprop(False)))))
          -∗ G (ITree.vis e k) Φ) -∗
      ∀ t Φ, wpi GF H t Φ -∗ G t Φ) := by
  iintro #HRet #HDiv #HVis
  iapply (wpi_iter_emp (H := H) G hne)
  iintro !> %t %Φ
  /- One case analysis on the node, shared by every client. -/
  induction t using ITree.cases
  · rename_i r
    /- `ITree.cases` phrases the return case with `Pure.pure`, which is
    definitionally `ITree.ret` (`instance : Monad (ITree E) where pure := ITree.ret`). -/
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

/-! ## Ghost updates

A `wpi` absorbs an update on either side. Both are biconditionals, and both are
consequences of the `|={∅}=>` sitting at every node of `wpiAcc`. -/

/-- `wpi_update_emp_mask`. -/
theorem wpi_update_emp (t : ITree E α) (Φ : Post GF α) :
    iprop(|={∅}=> wpi GF H t Φ) ⊣⊢ wpi GF H t Φ := by
  constructor
  · /- The `|={∅}=>` at the node absorbs the outer one. -/
    refine .trans (BIFUpdate.mono (wpi_unfold_emp t Φ).mp) ?_
    refine .trans ?_ (wpi_unfold_emp t Φ).mpr
    simp only [wpiAcc]
    exact BIFUpdate.trans
  · exact Iris.fupd_intro

/-- `wpi_update`. -/
theorem wpi_update (t : ITree E α) (Φ : Post GF α) (M : CoPset) :
    iprop(|={M}=> wpi_mask GF H t Φ M) ⊣⊢ wpi_mask GF H t Φ M := by
  constructor
  · simp only [wpi_mask]; exact BIFUpdate.trans
  · exact Iris.fupd_intro

/-! ## Consequence -/

/-- `wpi_upd_wand_emp_mask`: the strongest consequence rule, weakening under an
update. `wpi_wand_emp` is the special case. -/
theorem wpi_upd_wand_emp (t : ITree E α) (Φ Ψ : Post GF α) :
    iprop(∀ v, (|={∅}=> Φ v) -∗ (|={∅}=> Ψ v)) ⊢ iprop(wpi GF H t Φ -∗ wpi GF H t Ψ) := by
  /- `wpi.v:287`: generalise over the target postcondition, so that the induction
  hypothesis is available under the handler's continuations. -/
  iintro Hwand Hwp
  ihave Hgen :
      iprop(∀ (t' : ITree E α) (Φ' : Post GF α),
        wpi GF H t' Φ' -∗
        ∀ Ψ' : Post GF α, (∀ v, (|={∅}=> Φ' v) -∗ (|={∅}=> Ψ' v)) -∗ wpi GF H t' Ψ') $$ []
  · iapply (wpi_iter_emp' (H := H)
      (G := fun t' Φ' => iprop(∀ Ψ' : Post GF α,
        (∀ v, (|={∅}=> Φ' v) -∗ (|={∅}=> Ψ' v)) -∗ wpi GF H t' Ψ')))
    · intro t'
      constructor
      intro n Φ₁ Φ₂ hΦ
      refine BI.forall_ne fun Ψ' => BI.wand_ne.ne ?_ .rfl
      exact BI.forall_ne fun v => BI.wand_ne.ne (BIFUpdate.ne.ne (hΦ v)) .rfl
    · /- ret -/
      iintro !> %Φ' %v HΦ %Ψ' Hw
      iapply (wpi_ret_emp' (H := H) v Ψ').mp
      iapply Hw $$ HΦ
    · /- div: the hypothesis is `|={∅}=> False`, which entails anything. -/
      iintro !> %Φ' HF %Ψ' _
      iapply (wpi_div_emp (H := H) Ψ').mpr
      iexact HF
    · /- vis: push the weakening into both continuations. -/
      /- `Hw` is needed only by the sequential continuation; the spawning one has
      postcondition `False`, so it can be weakened with a trivial wand. -/
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
    iprop(∀ v, Φ v -∗ Ψ v) ⊢ iprop(wpi GF H t Φ -∗ wpi GF H t Ψ) := by
  iintro Hw
  iapply wpi_upd_wand_emp
  iintro %v HΦ
  imod HΦ with HΦ
  imodintro
  iapply Hw $$ HΦ

/-- Pointwise monotonicity: the form of the consequence rule that is convenient
for term-level reasoning, where the side condition is an entailment rather than a
wand. -/
theorem wpi_mono_emp {Φ Ψ : Post GF α} (t : ITree E α) (h : ∀ v, Φ v ⊢ Ψ v) :
    wpi GF H t Φ ⊢ wpi GF H t Ψ := by
  iintro Hwp
  iapply wpi_wand_emp $$ [] Hwp
  iintro %v
  iapply BI.entails_wand (h v)

/-- `wpi_wand`. **This is the rule the user asked for: lifting the
postcondition.** -/
theorem wpi_wand (t : ITree E α) (Φ Ψ : Post GF α) (M : CoPset) :
    iprop(∀ v, Φ v -∗ Ψ v) ⊢ iprop(wpi_mask GF H t Φ M -∗ wpi_mask GF H t Ψ M) := by
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
    wpi GF H t (fun v => iprop(|={∅}=> Φ v)) ⊣⊢ wpi GF H t Φ := by
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
    wpi_mask GF H t (fun v => iprop(|={M}=> Φ v)) M ⊣⊢ wpi_mask GF H t Φ M := by
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

/-! ## Handler refinement

`wpi_wandH` of `wpi.v:733`. The Coq proof goes through `wpi_translation` at the
identity interpretation; here the effect signature does not change, so the
`wpi_iter_emp'` iterator proves it directly and no `interp` is needed. -/

/-- `wpi_wandH_emp_mask`. -/
theorem wpi_wandH_emp {H₁ H₂ : Handler E GF} [W : wandH H₁ H₂]
    (t : ITree E α) (Φ : Post GF α) :
    wpi GF H₁ t Φ ⊢ wpi GF H₂ t Φ := by
  ihave Hgen : iprop(∀ (t' : ITree E α) (Φ' : Post GF α),
      wpi GF H₁ t' Φ' -∗ wpi GF H₂ t' Φ') $$ []
  · iapply (wpi_iter_emp' (H := H₁) (G := fun t' Φ' => wpi GF H₂ t' Φ'))
    · /- `wpi` is non-expansive in its postcondition because the least fixpoint
      is non-expansive in its index, and the index's tree component is fixed. -/
      intro t'
      constructor
      intro n Φ₁ Φ₂ hΦ
      simp only [wpi]
      exact OFE.NonExpansive.ne (f := bi_least_fixpoint (wpiAcc GF H₂)) ⟨.rfl, hΦ⟩
    · /- ret -/
      iintro !> %Φ' %v HΦ
      iapply (wpi_ret_emp' (H := H₂) v Φ').mp
      iexact HΦ
    · /- div -/
      iintro !> %Φ' HF
      iapply (wpi_div_emp (H := H₂) Φ').mpr
      iexact HF
    · /- vis: the only place `wandH` is used. -/
      iintro !> %Φ' %e %k HH
      iapply (wpi_vis_emp' (H := H₂) e k Φ').mp
      imod HH with HH
      imodintro
      iapply W.is_wandH e
      iexact HH
  iintro Hwp
  iapply Hgen $$ %t %Φ Hwp

/-- `wpi_wandH`. -/
theorem wpi_wandH {H₁ H₂ : Handler E GF} [wandH H₁ H₂]
    (t : ITree E α) (Φ : Post GF α) (M : CoPset) :
    wpi_mask GF H₁ t Φ M ⊢ wpi_mask GF H₂ t Φ M := by
  simp only [wpi_mask]
  exact BIFUpdate.mono (wpi_wandH_emp t _)

/-! ## Masked stepping rules for `vis`

These need the consequence and ghost-update rules above, so they come here rather
than with the other stepping rules. -/

/-- `wpi_vis'`. At a general mask the node is where the mask is *closed*: the
handler runs at `∅` and the postcondition reopens it. This is the formal content
of "atomicity is the distance between yields". -/
theorem wpi_vis' (e : E.I) (k : E.O e → ITree E α) (Φ : Post GF α) (M : CoPset) :
    iprop(|={M, ∅}=> H.run e
        (fun a => wpi_mask GF H (k a) (fun v => iprop(|={∅, M}=> Φ v)) ∅)
        (fun a => wpi_mask GF H (k a) (fun _ => iprop(False)) ⊤))
      ⊣⊢ wpi_mask GF H (ITree.vis e k) Φ M := by
  simp only [wpi_mask]
  constructor
  · /- Every step mirrors `wpi.v`'s proof of `wpi_vis'`. -/
    refine BIFUpdate.mono
      (.trans ?_ (.trans Iris.fupd_intro (wpi_vis_emp' (H := H) e k _).mp))
    iintro HH
    iapply H.mono e $$ [] [] HH
    · /- Sequential: `|={∅,∅}=>` on both node and postcondition collapse. -/
      iintro %a Hwp
      iapply (wpi_update_emp (H := H) (k a) _).mp
      imod Hwp with Hwp
      imodintro
      iapply (wpi_update_post_emp (H := H) (k a) _).mp $$ Hwp
    · /- Spawning: the postcondition is `False`, and `False` licenses any mask. -/
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
        (fun a => wpi_mask GF H (k a) (fun v => iprop(|={∅, M}=> Φ v)) ∅)
        (fun a => wpi_mask GF H (k a) (fun _ => iprop(False)) ⊤))
      ⊢ wpi_mask GF H (ITree.vis e k) Φ M :=
  (wpi_vis' e k Φ M).mp

/-- `wpi_trigger`: the rule an effect library actually uses. Triggering an event
of a sub-effect `E'` needs only `E'`'s own handler, provided that handler is
embedded in `H`.

The `inH`-style side condition of the Coq development is left as an explicit
hypothesis `hrun` until `Handler.sum` gets its projection lemmas. -/
theorem wpi_trigger {E' : Effect} [Sub : E' -< E] (e : E'.I) (Φ : Post GF (E'.O e))
    (M : CoPset) (H' : Handler E' GF)
    (hrun : ∀ (Ψ B : E'.O e → IProp GF),
      H'.run e Ψ B ⊢ H.run (Subeffect.map (E₁ := E') e).1
        (fun x => Ψ ((Subeffect.map (E₁ := E') e).2 x))
        (fun x => B ((Subeffect.map (E₁ := E') e).2 x))) :
    iprop(|={M, ∅}=> H'.run e (fun a => iprop(|={∅, M}=> Φ a)) (fun _ => iprop(False)))
      ⊢ wpi_mask GF H (Effect.trigger E' e) Φ M := by
  /- `Effect.trigger` is by definition a `vis` node whose continuation returns
  immediately, so this is `wpi_vis` composed with `wpi_ret`. -/
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

/-- `wpi_trigger`, with the side condition discharged by instance search rather
than passed by hand. This is the form clients use. -/
theorem wpi_trigger' {E' : Effect} [E' -< E] {H' : Handler E' GF} [inH H' H]
    (e : E'.I) (Φ : Post GF (E'.O e)) (M : CoPset) :
    iprop(|={M, ∅}=> H'.run e (fun a => iprop(|={∅, M}=> Φ a)) (fun _ => iprop(False)))
      ⊢ wpi_mask GF H (Effect.trigger E' e) Φ M :=
  wpi_trigger e Φ M H' (inH.embed e)

/-! ## Sequencing -/

/-- `wpi_bind_emp_mask`. -/
theorem wpi_bind_emp (t : ITree E α) (k : α → ITree E β) (Φ : Post GF β) :
    wpi GF H t (fun v => wpi GF H (k v) Φ) ⊢ wpi GF H (ITree.bind t k) Φ := by
  /- `wpi.v:325`: generalise over *both* the continuation and the outer
  postcondition, so that the induction hypothesis applies under the handler. -/
  iintro Hwp
  ihave Hgen :
      iprop(∀ (t' : ITree E α) (Φ' : Post GF α),
        wpi GF H t' Φ' -∗
        ∀ (Ψ : Post GF β) (k' : α → ITree E β),
          (∀ v, Φ' v -∗ wpi GF H (k' v) Ψ) -∗ wpi GF H (ITree.bind t' k') Ψ) $$ []
  · iapply (wpi_iter_emp' (H := H)
      (G := fun t' Φ' => iprop(∀ (Ψ : Post GF β) (k' : α → ITree E β),
        (∀ v, Φ' v -∗ wpi GF H (k' v) Ψ) -∗ wpi GF H (ITree.bind t' k') Ψ)))
    · intro t'
      constructor
      intro n Φ₁ Φ₂ hΦ
      refine BI.forall_ne fun Ψ => BI.forall_ne fun k' => BI.wand_ne.ne ?_ .rfl
      exact BI.forall_ne fun v => BI.wand_ne.ne (hΦ v) .rfl
    · /- ret: `bind (ret v) k' = k' v`, so the continuation's spec applies directly. -/
      iintro !> %Φ' %v HΦ %Ψ %k' Hw
      simp only [itree_ret_bind]
      iapply (wpi_update_emp (H := H) (k' v) Ψ).mp
      imod HΦ with HΦ
      imodintro
      iapply Hw $$ HΦ
    · /- div: `bind div k' = div`. -/
      iintro !> %Φ' HF %Ψ %k' _
      simp only [itree_div_bind]
      iapply (wpi_div_emp (H := H) Ψ).mpr
      iexact HF
    · /- vis: `bind (vis e k) k' = vis e (fun o => bind (k o) k')`. -/
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
  · /- Instantiate the generalised statement at the identity continuation spec. -/
    iapply Hgen $$ %t %(fun v => wpi GF H (k v) Φ) Hwp %Φ %k
    iintro %v HΦ
    iexact HΦ

/-- `wpi_bind`. The mask is the *same* on the outside, on the inside, and in the
intermediate postcondition: sequential composition never changes it. -/
theorem wpi_bind (t : ITree E α) (k : α → ITree E β) (Φ : Post GF β) (M : CoPset) :
    wpi_mask GF H t (fun v => wpi_mask GF H (k v) Φ M) M
      ⊢ wpi_mask GF H (ITree.bind t k) Φ M := by
  simp only [wpi_mask]
  refine BIFUpdate.mono (.trans ?_ (wpi_bind_emp (H := H) t k _))
  exact wpi_mono_emp t fun v =>
    .trans BIFUpdate.trans (wpi_update_emp (H := H) (k v) _).mp

/-! ## Framing

Both are corollaries of the consequence rule; they hold *because* `wpiAcc` is
monotone, which is the content of the `mono` field of `Handler`. -/

/-- `wpi_frame_l_emp_mask`. -/
theorem wpi_frame_l_emp (t : ITree E α) (Φ : Post GF α) (P : IProp GF) :
    iprop(P ∗ wpi GF H t Φ) ⊢ wpi GF H t (fun v => iprop(P ∗ Φ v)) := by
  iintro ⟨HP, Hwp⟩
  iapply wpi_wand_emp $$ [HP] Hwp
  iintro %v HΦ
  isplitl [HP]
  · iexact HP
  · iexact HΦ

/-- `wpi_frame_r_emp_mask`. -/
theorem wpi_frame_r_emp (t : ITree E α) (Φ : Post GF α) (P : IProp GF) :
    iprop(wpi GF H t Φ ∗ P) ⊢ wpi GF H t (fun v => iprop(Φ v ∗ P)) := by
  iintro ⟨Hwp, HP⟩
  iapply wpi_wand_emp $$ [HP] Hwp
  iintro %v HΦ
  isplitl [HΦ]
  · iexact HΦ
  · iexact HP

/-- `wpi_frame_l`. -/
theorem wpi_frame_l (t : ITree E α) (Φ : Post GF α) (P : IProp GF) (M : CoPset) :
    iprop(P ∗ wpi_mask GF H t Φ M) ⊢ wpi_mask GF H t (fun v => iprop(P ∗ Φ v)) M := by
  iintro ⟨HP, Hwp⟩
  iapply wpi_wand $$ [HP] Hwp
  iintro %v HΦ
  isplitl [HP]
  · iexact HP
  · iexact HΦ

/-- `wpi_frame_r`. -/
theorem wpi_frame_r (t : ITree E α) (Φ : Post GF α) (P : IProp GF) (M : CoPset) :
    iprop(wpi_mask GF H t Φ M ∗ P) ⊢ wpi_mask GF H t (fun v => iprop(Φ v ∗ P)) M := by
  iintro ⟨Hwp, HP⟩
  iapply wpi_wand $$ [HP] Hwp
  iintro %v HΦ
  isplitl [HΦ]
  · iexact HΦ
  · iexact HP

/-! ## Masks

`wpi_clear_mask` is the rule the paper flags as surprising: unlike Iris's
`wp_atomic` it is a *biconditional* and carries **no** `Atomic` side condition.
The authors' own note asks whether it should be renamed `wpi_atomic`. The reason
it holds unconditionally is that in an ITree every event is a single node, so
every event is atomic by construction. -/

/-- `wpi_reduce_mask`. -/
theorem wpi_reduce_mask (t : ITree E α) (Φ : Post GF α) (M M' : CoPset) :
    iprop(|={M, M'}=> wpi_mask GF H t (fun v => iprop(|={M', M}=> Φ v)) M')
      ⊢ wpi_mask GF H t Φ M := by
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
    iprop(|={M, ∅}=> wpi_mask GF H t (fun v => iprop(|={∅, M}=> Φ v)) ∅)
      ⊣⊢ wpi_mask GF H t Φ M := by
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
  · /- Inserting a trivial `|={∅}=>` on both the node and the postcondition. -/
    exact BIFUpdate.mono
      (((wpi_update_post_emp (H := H) t _).mpr).trans Iris.fupd_intro)

/-- `wpi_mask_mono`. -/
theorem wpi_mask_mono (t : ITree E α) (Φ : Post GF α) (M M' : CoPset)
    (hsub : M ⊆ M') :
    wpi_mask GF H t Φ M ⊢ wpi_mask GF H t Φ M' := by
  iintro Hwp
  iapply (wpi_reduce_mask (H := H) t Φ M' M)
  iapply (Iris.fupd_mask_intro (E1 := M') (E2 := M) hsub)
  iintro Hclose
  /- The closing update is threaded through the postcondition. -/
  iapply wpi_wand $$ [Hclose] Hwp
  iintro %v HΦ
  imod Hclose with _
  imodintro
  iexact HΦ

/-! ## Invariants

Neither rule needs the weakest precondition to issue a `▷`: the later comes from
`inv_acc`. And since `pointsTo` is `Timeless` in iris-lean, the second rule
covers most uses. -/

/-- `wpi_open_invariant`. -/
theorem wpi_open_invariant (N : Namespace) (M : CoPset)
    (t : ITree E α) (Φ : Post GF α) (P : IProp GF) (hsub : (↑N : CoPset) ⊆ M) :
    ⊢ iprop(Iris.inv N P -∗
        (▷ P -∗ wpi_mask GF H t (fun v => iprop(▷ P ∗ Φ v)) (SDiff.sdiff M (↑N : CoPset))) -∗
        wpi_mask GF H t Φ M) := by
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
        (P -∗ wpi_mask GF H t (fun v => iprop(P ∗ Φ v)) (SDiff.sdiff M (↑N : CoPset))) -∗
        wpi_mask GF H t Φ M) := by
  /- `wpi_mask` begins with a fancy update, hence absorbs `◇`. Registering that
  locally is what lets `elimModal_timeless` strip the `▷` from a `Timeless`
  resource without unfolding anything. -/
  letI : Iris.ProofMode.IsExcept0 (wpi_mask GF H t (fun v => iprop(P ∗ Φ v))
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

/-! ## The `step` event

`wpi_step` from `src/step.v`: the rule that makes `▷` available, and with it
Löb induction. Whether a `▷` is actually issued is the handler's choice — see
`AeneasIris.Step.LaterModality`. -/

end Rules

end AeneasIris
