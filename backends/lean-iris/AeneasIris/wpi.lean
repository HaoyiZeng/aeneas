/- Note: we deliberately do *not* `import Iris` (the umbrella module), because it
re-exports `Iris.Tests` and `Iris.Examples`. Those are broken in the current
iris-lean checkout (`#guard_msgs` pretty-printer drift) and are irrelevant here. -/
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

/- `u` is the effect's universe, `v` the return-type universe. They are kept
**separate**: an operation over a `Type u` state may still return `Unit` or
`Bool`, which live at `Type 0`. Naming them rather than writing `Type _` makes
them ordinary universe parameters shared by every declaration below, so
unification has one variable to solve instead of a fresh one per lemma. -/
universe u v

/-- Debit modality -/
notation:max "🧾" P:max => iprop(|={∅, ⊤}=> P)
/-- Gift modality -/
notation:max "💰" P:max => iprop(|={⊤, ∅}=> P)
/-- Blocking modality -/
notation:max "🧱" P:max => iprop(|={∅, ⊤}=> |={⊤, ∅}=> P)


variable (GF : BundledGFunctors) [Iris.InvGS_gen hlc GF] (E : Effect)

structure Handler (E : Effect) (GF : BundledGFunctors) where
  run : (i : E.I) → (E.O i → IProp GF) → (E.O i → IProp GF) → IProp GF
  mono : ∀ (i : E.I) (Ψ Ψ' Ψs Ψs' : E.O i → IProp GF),
    (∀ o, Ψ o -∗ Ψ' o) -∗  □ (∀ o, Ψs o -∗ Ψs' o) -∗ run i Ψ Ψs -∗ run i Ψ' Ψs'

/-- `sumH` of `handler.v`. `GF` is bound here rather than taken from the section
variable: the section binds it *explicitly*, which would put `H1` in its slot and
make the `⊕ₕ` notation ill-typed. -/
def Handler.sum {GF : BundledGFunctors} {E1 E2 : Effect}
    (H1 : Handler E1 GF) (H2 : Handler E2 GF) : Handler (E1 ⊕ₑ E2) GF where
  run i  := match i with | .inl i1 => H1.run i1  | .inr i2 => H2.run i2
  mono i := match i with | .inl i1 => H1.mono i1 | .inr i2 => H2.mono i2
infixr:30 " ⊕ₕ " => Handler.sum

/-! ### `inH`: one handler sits inside another

`inH H₁ H₂` says that on `E₁`-events, `H₂` does exactly what `H₁` does. This is
`handler.v`'s `inH`, and like there it is a **biconditional** — the reverse
direction is what the effect-translation rules need — and a *class*, so that
the instances below discharge it by structure rather than by hand. -/

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

/-- The direction `wpi_trigger` consumes. -/
theorem inH.embed {GF : BundledGFunctors} {E₁ E₂ : Effect} [E₁ -< E₂]
    {H₁ : Handler E₁ GF} {H₂ : Handler E₂ GF}
    [I : inH H₁ H₂] (e : E₁.I) (Ψ B : E₁.O e → IProp GF) :
    H₁.run e Ψ B ⊢ H₂.run (Subeffect.ev e) (fun x => Ψ (Subeffect.ans e x))
                                           (fun x => B (Subeffect.ans e x)) :=
  (I.is_inH e Ψ B).mpr

instance inH_refl {GF : BundledGFunctors} {E : Effect} (H : Handler E GF) : inH H H where
  is_inH _ _ _ := .rfl

/-- Recursive, not a plain left injection: this is what lets a *nested* sum such
as `FailE ⊕ₑ (StateE ⊕ₑ ConcE)` resolve. -/
instance sumH_inH_l {GF : BundledGFunctors} {E₁ E₂ E₃ : Effect} [E₁ -< E₂]
    (H₁ : Handler E₁ GF) (H₂ : Handler E₂ GF) (H₃ : Handler E₃ GF) [I : inH H₁ H₂] :
    inH H₁ (H₂ ⊕ₕ H₃) where
  is_inH e Ψ B := I.is_inH e Ψ B

instance sumH_inH_r {GF : BundledGFunctors} {E₁ E₂ E₃ : Effect} [E₁ -< E₃]
    (H₁ : Handler E₁ GF) (H₂ : Handler E₂ GF) (H₃ : Handler E₃ GF) [I : inH H₁ H₃] :
    inH H₁ (H₂ ⊕ₕ H₃) where
  is_inH e Ψ B := I.is_inH e Ψ B

/-! ### `wandH`: one handler is stronger than another

`handler.v`'s `wandH`. Unlike `inH` this is *within one* effect signature and
one-directional: `H₁` demands at least as much as `H₂` at every event, so a
weakest precondition taken with `H₁` is also one taken with `H₂`
(`wpi_wandH` in `AeneasIris.Rules`). This is what handler refinement means. -/

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

/-! ### Handlers are non-expansive in their continuations

This does not have to be assumed. The trick (`handler_ne` in the Coq
development, `src/handler.v`) is to characterise `H.run e Ψ B` by an equivalent
form in which `Ψ` and `B` occur only *positively* — the handler itself is applied
to freshly quantified `Ψ'`/`B'`, and the originals appear only on the right of a
wand. Congruence then goes straight through. -/

theorem Handler.run_eq {GF : BundledGFunctors} {E : Effect}
    (H : Handler E GF) (e : E.I) (Ψ B : E.O e → IProp GF) :
    H.run e Ψ B ⊣⊢
      iprop(∃ Ψ' B', (∀ a, Ψ' a -∗ Ψ a) ∗ □ (∀ a, B' a -∗ B a) ∗ H.run e Ψ' B') := by
  constructor
  · /- Take `Ψ' := Ψ` and `B' := B`; both wands are the identity. -/
    iintro HH
    iexists Ψ, B
    isplitr [HH]
    · iintro %a HΨ; iexact HΨ
    · isplitr [HH]
      · imodintro; iintro %a HB; iexact HB
      · iexact HH
  · /- This direction is exactly `HandlerMono`. -/
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


-- class inH (H₁ : Handler E₁ GF) (H₂ : Handler E₂ GF) where
--   is_inH : ∀ A e Φ s, H₂ A (subevent A e) Φ s ⊣⊢ H₁ A e Φ s.




/-! ### Generic machinery

Everything here is generic in the effect signature and the handler. A concrete
language is assembled elsewhere — see `AeneasIris.Concurrency` — by choosing an
effect signature and the matching handler; adding another effect touches nothing
in this file. -/

abbrev Post α := (α -> IProp GF)
abbrev Pre := IProp GF
abbrev WpIdx (E : Effect.{u}) (α : Type v) : Type _ :=
  LeibnizO (ITree E α) × Post GF α

def wpiAcc {E : Effect.{u}} {α : Type v} (H : Handler E GF)
  (F : WpIdx GF E α → IProp GF) : WpIdx GF E α → IProp GF :=
  fun p => iprop%
  |={∅}=>
  match p.1.car.unfold with
  | .ret x => p.2 x
  | .div => iprop% False
  | .vis e k =>
    H.run e
      (λ a => F (⟨k a⟩, p.2))
      (λ a => iprop% |={⊤, ∅}=> F (⟨k a⟩, (λ _ => iprop% False)))

/-- The core semantic obligation: given `HandlerMono`, the functional whose least
fixpoint is `wpi` is monotone. This is what makes the structural rules — the frame
rule in particular — hold for free. -/
instance wpi_mono {E : Effect.{u}} {α : Type v} (H : Handler E GF) :
    BIMonoPred (wpiAcc GF H (α := α)) := by
  constructor
  case mono_pred =>
    intro Φ Ψ _ _
    iintro #Hmono %p
    simp only [wpiAcc]
    cases hu : p.fst.car.unfold
    · /- ret: the postcondition does not mention the recursive occurrence. -/
      iintro HF; imod HF with HF; imodintro; iexact HF
    · /- div: `False`, likewise. -/
      iintro HF; imod HF with HF; imodintro; iexact HF
    · /- vis: the only interesting case, and it is exactly `HandlerMono`. Note the
      spawning continuation needs `Hmono` a second time, which is possible because
      `Hmono` is under `□`. -/
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
    /- Non-expansiveness of `wpiAcc H Φ`. The `ret` and `div` cases are immediate
    (the tree component is discrete, so `p.fst = q.fst`); the `vis` case needs the
    handler to be non-expansive in its continuations. That does *not* have to be
    assumed: it follows from `HandlerMono`, by rewriting `H e Ψ B` as
      `∃ Ψ' B', (∀ a, Ψ' a -∗ Ψ a) ∗ □ (∀ a, B' a -∗ B a) ∗ H e Ψ' B'`
    in which every occurrence of `Ψ` and `B` is positive, and then congruence.
    See `Handler.run_ne` above. -/
    intro Φ' _
    constructor
    intro n p q hpq
    obtain ⟨ht, hΦ⟩ := hpq
    /- The tree component is `LeibnizO`, hence discrete: `n`-equivalence is equality. -/
    have hfst : p.fst = q.fst :=
      OFE.eq_of_eqv (OFE.discrete_0 (OFE.Dist.le ht (Nat.zero_le n)))
    simp only [wpiAcc, hfst]
    /- The `|={∅}=>` at the node is non-expansive, so peel it off and recurse. -/
    refine BIFUpdate.ne.ne ?_
    cases q.fst.car.unfold
    · exact hΦ _
    · exact .rfl
    · rename_i e k
      exact Handler.run_ne H e (fun a => OFE.NonExpansive.ne (by exact ⟨.rfl, hΦ⟩))
                               (fun a => .rfl)

def wpi {E : Effect.{u}} {α : Type v} (H : Handler E GF)
  (t : ITree E α)
  (Φ : Post GF α) : IProp GF :=
    bi_least_fixpoint (wpiAcc GF H) (⟨t⟩, Φ)

def wpi_mask {E : Effect.{u}} {α : Type v} (H : Handler E GF)
  (t : ITree E α)
  (Φ : Post GF α) (E : CoPset) : IProp GF := iprop%
    |={E, ∅}=> wpi GF H t iprop(λ v => |={∅, E}=> Φ v)


end AeneasIris
