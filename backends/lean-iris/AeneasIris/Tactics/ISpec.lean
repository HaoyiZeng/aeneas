import AeneasIris.Rules
import Aeneas.Std.WP
import Aeneas.Std.Spec
import Aeneas.Tactic.Step.Step

/-! # `iSpec`: `wpi` as a spec judgment Aeneas' `step` tactic understands -/

namespace AeneasIris

open Iris BI Aeneas.Data.Coinductive
open Aeneas.Std (Result RustEffect)

unseal Aeneas.Std.Result

/-! ## The judgment -/

def iSpec {hlc : Iris.HasLC} {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]
    {E : Effect} {α : Type} (H : Handler E GF) (m : Mode) (P : IProp GF)
    (t : ITree E α) (Φ : Post GF α) (M : CoPset) : Prop :=
  P ⊢ wpi_mask GF H m t Φ M

/-- The Iris counterpart of `qimp`. -/
def iqimp {hlc : Iris.HasLC} {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]
    {α : Type} (Φ Ψ : Post GF α) : Prop :=
  ∀ v, Φ v ⊢ Ψ v

/-- The Iris counterpart of `qimp_spec`. -/
def iqimp_spec {hlc : Iris.HasLC} {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]
    {α β : Type} (H : Handler RustEffect GF) (m : Mode)
    (Φ : Post GF α) (k : α → Result β) (Ψ : Post GF β) (M : CoPset) : Prop :=
  ∀ v, Φ v ⊢ wpi_mask GF H m (k v) Ψ M

/-! ## The two lemmas `step` needs -/

/-- `mk_spec_mono`. -/
theorem iSpec_mono' {hlc : Iris.HasLC} {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]
    {α : Type} {H : Handler RustEffect GF} {P : IProp GF} {M : CoPset} {Ψ : Post GF α}
    {t : Result α} {Φ : Post GF α}
    (h : iSpec H m P t Φ M) (hq : iqimp Φ Ψ) : iSpec H m P t Ψ M := by
  refine .trans h ?_
  iintro Hwp
  iapply (wpi_wand (H := H) t Φ Ψ M) $$ [] Hwp
  iintro %v HΦ
  iapply BI.entails_wand (hq v)
  iexact HΦ

/-- `mk_spec_bind`. -/
theorem iSpec_bind' {hlc : Iris.HasLC} {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]
    {α β : Type} {H : Handler RustEffect GF} {P : IProp GF} {M : CoPset}
    {k : α → Result β} {Ψ : Post GF β} {t : Result α} {Φ : Post GF α}
    (h : iSpec H m P t Φ M) (hk : iqimp_spec H m Φ k Ψ M) :
    iSpec H m P ((t >>= k : Result β)) Ψ M := by
  refine .trans h ?_
  show _ ⊢ wpi_mask GF H m (ITree.bind t k) Ψ M
  refine .trans ?_ (wpi_bind (H := H) t k Ψ M)
  iintro Hwp
  iapply (wpi_wand (H := H) t Φ (fun v => wpi_mask GF H m (k v) Ψ M) M) $$ [] Hwp
  iintro %v HΦ
  iapply BI.entails_wand (hk v)
  iexact HΦ

/-! ## The eliminations -/

theorem iqimp_iff {hlc : Iris.HasLC} {GF : BundledGFunctors}
    [Iris.InvGS_gen hlc GF] {α : Type} (Φ Ψ : Post GF α) :
    iqimp Φ Ψ ↔ ∀ v, Φ v ⊢ Ψ v := Iff.rfl

theorem iqimp_spec_def {hlc : Iris.HasLC} {GF : BundledGFunctors}
    [Iris.InvGS_gen hlc GF] {α β : Type} (H : Handler RustEffect GF) (m : Mode)
    (Φ : Post GF α) (k : α → Result β) (Ψ : Post GF β) (M : CoPset) :
    iqimp_spec H m Φ k Ψ M = ∀ v, Φ v ⊢ wpi_mask GF H m (k v) Ψ M := rfl

theorem entails_iSpec {hlc : Iris.HasLC} {GF : BundledGFunctors}
    [Iris.InvGS_gen hlc GF] {E : Effect} {α : Type} (H : Handler E GF) (m : Mode)
    (P : IProp GF) (t : ITree E α) (Φ : Post GF α) (M : CoPset) :
    (P ⊢ wpi_mask GF H m t Φ M) ↔ iSpec H m P t Φ M := Iff.rfl

/-- Recovers the precondition after a lifted pure call: the pure fact becomes a -/
theorem and_pure_entails_iff {GF : BundledGFunctors} (φ : Prop) (P W : IProp GF) :
    (iprop(⌜φ⌝ ∧ P) ⊢ W) ↔ (φ → (P ⊢ W)) := by
  constructor
  · intro h hφ
    exact .trans (BI.and_intro (BI.pure_intro hφ) .rfl) h
  · intro h
    exact BI.pure_elim_left h

theorem pure_entails_iff {GF : BundledGFunctors} (φ : Prop) (W : IProp GF) :
    (iprop(⌜φ⌝) ⊢ W) ↔ (φ → (⊢ W)) := by
  constructor
  · intro h hφ; exact .trans (BI.pure_intro hφ) h
  · intro h; exact BI.pure_elim' h

/-- Re-establish the head symbol `step` dispatches on. -/
theorem iSpec_intro {hlc : Iris.HasLC} {GF : BundledGFunctors}
    [Iris.InvGS_gen hlc GF] {α : Type} {H : Handler RustEffect GF} {P : IProp GF}
    {t : Result α} {Φ : Post GF α} {M : CoPset}
    (h : iSpec H m P t Φ M) : P ⊢ wpi_mask GF H m t Φ M := h

/-! ## The lifting -/

/-- Every `⦃⦄` lemma of the Aeneas standard library, as an `iSpec`. -/
theorem spec_to_iSpec {hlc : Iris.HasLC} {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]
    {H : Handler RustEffect GF} {P : IProp GF} {α : Type} {t : Result α}
    {p : Aeneas.Std.WP.Post α} {M : CoPset} (h : Aeneas.Std.WP.spec t p) :
    iSpec H m P t (fun v => iprop(⌜p v⌝ ∧ P)) M := by
  cases h
  rename_i x hp
  show _ ⊢ wpi_mask GF H m (ITree.ret x) _ M
  refine .trans ?_ (wpi_ret (H := H) x (fun v => iprop(⌜p v⌝ ∧ P)) M)
  exact BI.and_intro (BI.pure_intro hp) .rfl

@[simp] theorem iSpec_ok {hlc : Iris.HasLC} {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]
    {H : Handler RustEffect GF} {P : IProp GF} {α : Type}
    (v : α) (Φ : Post GF α) (M : CoPset) :
    iSpec H m P (Result.ok v) Φ M  ↔  (P ⊢ |={M}=> Φ v) := by
  unfold iSpec
  constructor
  · intro h; exact .trans h (wpi_ret' (H := H) v Φ M).mpr
  · intro h; exact .trans h (wpi_ret' (H := H) v Φ M).mp

/-! ## Registration -/

open Aeneas in
#register_spec_info {
    spec_name := ``AeneasIris.iSpec
    arity := 11
    program_index := 8
    post_index := 9
    mk_spec_mono := ``AeneasIris.iSpec_mono'
    mk_spec_mono_skip_args := 9
    mk_spec_bind := ``AeneasIris.iSpec_bind'
    mk_spec_bind_skip_args := 11
    uncurry_elim_tactics := #[]
    qimp_elim_tactics := #[``AeneasIris.iqimp_spec_def, ``AeneasIris.and_pure_entails_iff,
                           ``AeneasIris.iqimp_iff]
    to_mvcgen := .none
    liftings := #[
      { from_statement := ``Aeneas.Std.WP.spec
        conversion_thm := ``AeneasIris.spec_to_iSpec
        conversion_thm_inferred_args := 10 }
    ]
  }

end AeneasIris
