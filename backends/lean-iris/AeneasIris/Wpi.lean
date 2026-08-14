import Iris.Algebra
import Iris.BI
import Iris.Instances
import Iris.ProofMode
import Iris.Instances.IProp
import Iris.BI.Lib.Fixpoint

import Aeneas.Data.Coinductive.ITree
import Aeneas.Data.Coinductive.Effect
import Iris.Instances.Lib.Invariants

namespace AeneasIris

open Iris Aeneas.Data.Coinductive

universe u v

/-- Debit modality -/
notation:max "🧾" P:max => iprop(|={∅, ⊤}=> P)
/-- Gift modality -/
notation:max "💰" P:max => iprop(|={⊤, ∅}=> P)
/-- Blocking modality -/
notation:max "🧱" P:max => iprop(|={∅, ⊤}=> |={⊤, ∅}=> P)

variable (GF : BundledGFunctors) [Iris.InvGS_gen hlc GF] (E : Effect)

/-! ## `Mode`: the one termination-sensitivity knob -/

inductive Mode where
  /-- Total correctness: no `▷`, and divergence is a failure. -/
  | total
  /-- Partial correctness: `▷` at each step, and divergence owes nothing. -/
  | part
deriving DecidableEq, Repr, Inhabited

/-- What silent divergence is worth. -/
def divOK : Mode → IProp GF
  | .total     => iprop(False)
  | .part => iprop(True)

@[simp] theorem divOK_total : divOK GF .total = iprop(False) := rfl
@[simp] theorem divOK_partial : divOK GF .part = iprop(True) := rfl

structure Handler (E : Effect) (GF : BundledGFunctors) where
  run : (i : E.I) → (E.O i → IProp GF) → (E.O i → IProp GF) → IProp GF
  mono : ∀ (i : E.I) (Ψ Ψ' Ψs Ψs' : E.O i → IProp GF),
    (∀ o, Ψ o -∗ Ψ' o) -∗  □ (∀ o, Ψs o -∗ Ψs' o) -∗ run i Ψ Ψs -∗ run i Ψ' Ψs'

/-- `sumH` of `handler.v`. -/
def Handler.sum {GF : BundledGFunctors} {E1 E2 : Effect}
    (H1 : Handler E1 GF) (H2 : Handler E2 GF) : Handler (E1 ⊕ₑ E2) GF where
  run i  := match i with | .inl i1 => H1.run i1  | .inr i2 => H2.run i2
  mono i := match i with | .inl i1 => H1.mono i1 | .inr i2 => H2.mono i2
infixr:30 " ⊕ₕ " => Handler.sum

/-! ### `inH`: one handler sits inside another -/

/-- The image of an `E₁`-event in `E₂`. -/
abbrev Subeffect.ev {E₁ E₂ : Effect} [E₁ -< E₂] (e : E₁.I) : E₂.I :=
  (Subeffect.map (E₁ := E₁) e).1

/-- The answer map back from `E₂`'s answer to `E₁`'s. -/
abbrev Subeffect.ans {E₁ E₂ : Effect} [E₁ -< E₂] (e : E₁.I) :
    E₂.O (Subeffect.ev e) → E₁.O e :=
  (Subeffect.map (E₁ := E₁) e).2

class inH {GF : BundledGFunctors} {E₁ E₂ : Effect} [E₁ -< E₂]
    (H₁ : Handler E₁ GF) (H₂ : Handler E₂ GF) where
  is_inH : ∀ (e : E₁.I) (Ψ B : E₁.O e → IProp GF),
    H₂.run (Subeffect.ev e) (fun x => Ψ (Subeffect.ans e x))
                            (fun x => B (Subeffect.ans e x))
      ⊣⊢ H₁.run e Ψ B

@[inherit_doc] notation:50 H₁:51 " -<ₕ " H₂:51 => inH H₁ H₂

/-- The direction `wpi_trigger` consumes. -/
theorem inH.embed {GF : BundledGFunctors} {E₁ E₂ : Effect} [E₁ -< E₂]
    {H₁ : Handler E₁ GF} {H₂ : Handler E₂ GF}
    [I : H₁ -<ₕ H₂] (e : E₁.I) (Ψ B : E₁.O e → IProp GF) :
    H₁.run e Ψ B ⊢ H₂.run (Subeffect.ev e) (fun x => Ψ (Subeffect.ans e x))
                                           (fun x => B (Subeffect.ans e x)) :=
  (I.is_inH e Ψ B).mpr

instance inH_refl {GF : BundledGFunctors} {E : Effect} (H : Handler E GF) : inH H H where
  is_inH _ _ _ := .rfl

/-- Recursive, not a plain left injection: this is what lets a *nested* sum such -/
instance sumH_inH_l {GF : BundledGFunctors} {E₁ E₂ E₃ : Effect} [E₁ -< E₂]
    (H₁ : Handler E₁ GF) (H₂ : Handler E₂ GF) (H₃ : Handler E₃ GF) [I : H₁ -<ₕ H₂] :
    H₁ -<ₕ (H₂ ⊕ₕ H₃) where
  is_inH e Ψ B := I.is_inH e Ψ B

instance sumH_inH_r {GF : BundledGFunctors} {E₁ E₂ E₃ : Effect} [E₁ -< E₃]
    (H₁ : Handler E₁ GF) (H₂ : Handler E₂ GF) (H₃ : Handler E₃ GF) [I : H₁ -<ₕ H₃] :
    H₁ -<ₕ (H₂ ⊕ₕ H₃) where
  is_inH e Ψ B := I.is_inH e Ψ B

/-! ### `wandH`: one handler is stronger than another -/

class wandH {GF : BundledGFunctors} {E : Effect} (H₁ H₂ : Handler E GF) where
  is_wandH : ∀ (e : E.I) (Ψ B : E.O e → IProp GF), H₁.run e Ψ B ⊢ H₂.run e Ψ B

instance wandH_refl {GF : BundledGFunctors} {E : Effect} (H : Handler E GF) :
    wandH H H where
  is_wandH _ _ _ := .rfl

instance sumH_wandH {GF : BundledGFunctors} {E₁ E₂ : Effect}
    (H₁ H₁' : Handler E₁ GF) (H₂ H₂' : Handler E₂ GF)
    [W₁ : wandH H₁ H₁'] [W₂ : wandH H₂ H₂'] :
    wandH (H₁ ⊕ₕ H₂) (H₁' ⊕ₕ H₂') where
  is_wandH e Ψ B := match e with
    | .inl e₁ => W₁.is_wandH e₁ Ψ B
    | .inr e₂ => W₂.is_wandH e₂ Ψ B

/-! ### Handlers are non-expansive in their continuations -/

theorem Handler.run_eq {GF : BundledGFunctors} {E : Effect}
    (H : Handler E GF) (e : E.I) (Ψ B : E.O e → IProp GF) :
    H.run e Ψ B ⊣⊢
      iprop(∃ Ψ' B', (∀ a, Ψ' a -∗ Ψ a) ∗ □ (∀ a, B' a -∗ B a) ∗ H.run e Ψ' B') := by
  constructor
  ·
    iintro HH
    iexists Ψ, B
    isplitr [HH]
    · iintro %a HΨ; iexact HΨ
    · isplitr [HH]
      · imodintro; iintro %a HB; iexact HB
      · iexact HH
  ·
    iintro ⟨%Ψ', %B', Hw, #Hws, HH⟩
    iapply H.mono e Ψ' Ψ B' B $$ Hw Hws HH

theorem Handler.run_ne {GF : BundledGFunctors} {E : Effect}
    (H : Handler E GF) (e : E.I) {n}
    {Ψ Ψ' B B' : E.O e → IProp GF}
    (hΨ : ∀ a, Ψ a ≡{n}≡ Ψ' a) (hB : ∀ a, B a ≡{n}≡ B' a) :
    H.run e Ψ B ≡{n}≡ H.run e Ψ' B' := by
  have h1 := (BI.equiv_iff.mpr (Handler.run_eq H e Ψ B)).dist (n := n)
  have h2 := (BI.equiv_iff.mpr (Handler.run_eq H e Ψ' B')).dist (n := n)
  refine OFE.dist_eqv.3 h1 (OFE.dist_eqv.3 ?_ (OFE.dist_eqv.2 h2))
  exact BI.exists_ne fun _ => BI.exists_ne fun _ =>
    BI.sep_ne.ne (BI.forall_ne fun a => BI.wand_ne.ne .rfl (hΨ a))
      (BI.sep_ne.ne (BI.intuitionistically_ne.ne
        (BI.forall_ne fun a => BI.wand_ne.ne .rfl (hB a))) .rfl)

/-! ### Generic machinery -/

abbrev Post α := (α -> IProp GF)
abbrev Pre := IProp GF
abbrev WpIdx (E : Effect.{u}) (α : Type v) : Type _ :=
  LeibnizO (ITree E α) × Post GF α

/-! ### Termination sensitivity, as one knob -/

def wpiAcc {E : Effect.{u}} {α : Type v} (H : Handler E GF) (m : Mode)
  (F : WpIdx GF E α → IProp GF) : WpIdx GF E α → IProp GF :=
  fun p => iprop%
  |={∅}=>
  match p.1.car.unfold with
  | .ret x => p.2 x
  | .div => divOK GF m
  | .vis e k =>
    H.run e
      (λ a => F (⟨k a⟩, p.2))
      (λ a => iprop% |={⊤, ∅}=> F (⟨k a⟩, (λ _ => iprop% False)))

/-- The core semantic obligation: given `HandlerMono`, the functional whose least -/
instance wpi_mono {E : Effect.{u}} {α : Type v} (H : Handler E GF) (m : Mode) :
    BIMonoPred (wpiAcc GF H m (α := α)) := by
  constructor
  case mono_pred =>
    intro Φ Ψ _ _
    iintro #Hmono %p
    simp only [wpiAcc]
    cases hu : p.fst.car.unfold
    ·
      iintro HF; imod HF with HF; imodintro; iexact HF
    ·
      iintro HF; imod HF with HF; imodintro; iexact HF
    ·
      rename_i e k
      iintro HF
      imod HF with HF
      imodintro
      iapply H.mono e
        (fun a => Φ (⟨k a⟩, p.snd))
        (fun a => Ψ (⟨k a⟩, p.snd))
        (fun a => iprop(|={⊤, ∅}=> Φ (⟨k a⟩, fun _ => iprop(False))))
        (fun a => iprop(|={⊤, ∅}=> Ψ (⟨k a⟩, fun _ => iprop(False))))
      · iintro %a HΦ; iapply Hmono $$ HΦ
      · imodintro; iintro %a HΦ; imod HΦ with HΦ; imodintro; iapply Hmono $$ HΦ
      · iexact HF
  case mono_pred_ne =>
    intro Φ' _
    constructor
    intro n p q hpq
    obtain ⟨ht, hΦ⟩ := hpq
    have hfst : p.fst = q.fst :=
      OFE.eq_of_eqv (OFE.discrete_0 (OFE.Dist.le ht (Nat.zero_le n)))
    simp only [wpiAcc, hfst]
    refine BIFUpdate.ne.ne ?_
    cases q.fst.car.unfold
    · exact hΦ _
    · exact .rfl
    · rename_i e k
      exact Handler.run_ne H e (fun a => OFE.NonExpansive.ne (by exact ⟨.rfl, hΦ⟩))
                               (fun a => .rfl)

def wpi {E : Effect.{u}} {α : Type v} (H : Handler E GF) (m : Mode)
  (t : ITree E α)
  (Φ : Post GF α) : IProp GF :=
    bi_least_fixpoint (wpiAcc GF H m) (⟨t⟩, Φ)

def wpi_mask {E : Effect.{u}} {α : Type v} (H : Handler E GF) (m : Mode)
  (t : ITree E α)
  (Φ : Post GF α) (E : CoPset) : IProp GF := iprop%
    |={E, ∅}=> wpi GF H m t iprop(λ v => |={∅, E}=> Φ v)

end AeneasIris
