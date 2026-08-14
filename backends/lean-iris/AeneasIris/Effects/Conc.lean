import Aeneas.Std.Effects
import AeneasIris.Wpi
import AeneasIris.Rules
import AeneasIris.Effects.Step
import Iris.Instances.Lib.Invariants

namespace AeneasIris.Conc

open Iris BI Aeneas.Data.Coinductive
open Aeneas.Std (ConcE StepE)

universe u v
open AeneasIris

variable (GF : BundledGFunctors) [Iris.InvGS_gen hlc GF]

/-! ## Operations -/

/-- The only point at which control may pass to another thread. -/
def yield {E : Effect.{v}} [ConcE.{v} -< E] : ITree E PUnit.{v+1} :=
  Effect.trigger ConcE.{v} .yield

/-- `yield` collapsed to `Unit`. -/
def yieldU {E : Effect.{v}} [ConcE.{v} -< E] : ITree E Unit :=
  ITree.bind (yield (E := E)) (fun _ => ITree.ret ())

/-- Poll until `attempt` succeeds, yielding in between. -/
noncomputable def waitUntil {E : Effect.{v}} [ConcE.{v} -< E] [StepE.{v} -< E]
    {α : Type u} (attempt : ITree E (Option α)) : ITree E α := do
  let o ← attempt
  match o with
  | some v => ITree.ret v
  | none =>
      ITree.bind (yieldU (E := E)) (fun _ =>
        ITree.bind (AeneasIris.Step.stepP.{u, v} (E := E)) (fun _ =>
          waitUntil attempt))
partial_fixpoint

/-- A synchronisation operation: yield first, then do it. -/
noncomputable def sync {E : Effect.{v}} [ConcE.{v} -< E] {α : Type u}
    (op : ITree E α) : ITree E α :=
  ITree.bind (yieldU (E := E)) (fun _ => op)

/-! ## The handler -/

section ConcHandler

def ConcH.run (i : ConcE.I) (Ψ Ψs : ConcE.O i → IProp GF) : IProp GF :=
  match i with
  | .fork => iprop%
    Ψ .cur ∗ Ψs .new
  | .yield => iprop%
    🧱 (Ψ .unit)
  | .endthread => iprop%
    🧾 True

def ConcH : Handler ConcE GF := {
  run := ConcH.run GF
  mono := by
    intro i Ψ Ψ' Ψs Ψs'
    cases i
    ·
      simp only [ConcH.run]
      iintro Hw #Hws ⟨HΨ, HΨs⟩
      isplitl [Hw HΨ]
      · iapply Hw $$ HΨ
      · iapply Hws $$ HΨs
    ·
      simp only [ConcH.run]
      iintro Hw _ H
      imod H with H
      imodintro
      imod H with H
      imodintro
      iapply Hw $$ H
    ·
      simp only [ConcH.run]
      iintro _ _ H
      iexact H
}
end ConcHandler

/-! ## Structural rules for the concurrency effect -/

section ConcRules

variable {E : Effect.{v}} {H : Handler E GF} [Sub : ConcE.{v} -< E]
variable [I : ConcH GF -<ₕ H]

/-- `wpi_yield`. -/
theorem wpi_yield (Φ : Post GF PUnit.{v+1}) :
    iprop(Φ PUnit.unit) ⊢ wpi_mask GF H m (yield (E := E)) Φ ⊤ := by
  simp only [yield]
  refine .trans ?_ (wpi_trigger (H := H) (E' := ConcE.{v}) (Sub := Sub)
    ConcE.I.yield Φ ⊤ (ConcH GF) (fun Ψ B => inH.embed (H₁ := ConcH GF) (H₂ := H) ConcE.I.yield Ψ B))
  have intro_mask := Iris.fupd_mask_intro_subseteq (PROP := IProp GF)
    (E1 := ⊤) (E2 := ∅) (P := iprop(Φ PUnit.unit)) Iris.Std.LawfulSet.empty_subset
  exact intro_mask.trans (BIFUpdate.mono (BIFUpdate.mono intro_mask))

/-- `wpi_yield` at `Unit`, for the collapsed `yieldU`. -/
theorem wpi_yieldU (Φ : Post GF Unit) :
    iprop(Φ ()) ⊢ wpi_mask GF H m (yieldU (E := E)) Φ ⊤ := by
  simp only [yieldU]
  refine .trans ?_ (wpi_bind (H := H) _ _ Φ ⊤)
  refine .trans ?_ (wpi_yield (H := H)
    (Φ := fun _ => wpi_mask GF H m (ITree.ret ()) Φ ⊤))
  exact wpi_ret (H := H) () Φ ⊤

/-- `wpi_sync`: a synchronisation operation costs one yield, hence mask `⊤`. -/
theorem wpi_sync {α : Type u} (op : ITree E α) (Φ : Post GF α) :
    wpi_mask GF H m op Φ ⊤ ⊢ wpi_mask GF H m (sync (E := E) op) Φ ⊤ := by
  simp only [sync]
  refine .trans ?_ (wpi_bind (H := H) _ _ Φ ⊤)
  exact wpi_yieldU (H := H) (Φ := fun _ => wpi_mask GF H m op Φ ⊤)

/-- `wpi_kill`: ending a thread proves anything. -/
theorem wpi_kill (kt : ConcE.O .endthread → ITree E α)
    (Φ : Post GF α) :
    iprop(True) ⊢ wpi_mask GF H m (ITree.bind (Effect.trigger ConcE .endthread) kt) Φ ⊤ := by
  refine .trans ?_ (wpi_bind (H := H) _ kt Φ ⊤)
  refine .trans ?_ (wpi_trigger (H := H) (E' := ConcE) (Sub := Sub)
    ConcE.I.endthread _ ⊤ (ConcH GF) (fun Ψ B => inH.embed (H₁ := ConcH GF) (H₂ := H) ConcE.I.endthread Ψ B))
  exact Iris.fupd_mask_intro_subseteq (E1 := ⊤) (E2 := ∅) (P := iprop(True))
    Iris.Std.LawfulSet.empty_subset

/-- `wpi_fork`. -/
theorem wpi_fork (kt : ConcE.O .fork → ITree E α)
    (Φ : Post GF α) (M : CoPset) :
    iprop(wpi_mask GF H m (kt .cur) Φ M ∗ wpi_mask GF H m (kt .new) (fun _ => iprop(False)) ⊤)
      ⊢ wpi_mask GF H m (ITree.bind (Effect.trigger ConcE .fork) kt) Φ M := by
  simp only [Effect.trigger, itree_vis_bind]
  refine .trans ?_ (wpi_vis (H := H) _ _ Φ M)
  have hred : ∀ (a : E.O (Subeffect.map (E₁ := ConcE) ConcE.I.fork).1),
      ITree.bind (Pure.pure ((Subeffect.map (E₁ := ConcE) ConcE.I.fork).snd a)) kt
        = kt ((Subeffect.map (E₁ := ConcE) ConcE.I.fork).snd a) :=
    fun a => itree_ret_bind _ _
  simp only [hred]
  refine .trans ?_ (BIFUpdate.mono (inH.embed (H₁ := ConcH GF) (H₂ := H) ConcE.I.fork
    (fun v => wpi_mask GF H m (kt v) (fun v => iprop(|={∅, M}=> Φ v)) ∅)
    (fun v => wpi_mask GF H m (kt v) (fun _ => iprop(False)) ⊤)))
  simp only [ConcH, ConcH.run]
  exact (BI.sep_mono_left (wpi_clear_mask (H := H) (kt ConcE.Tags.cur) Φ M).mpr).trans
    BIFUpdate.frame_right

/-- `spawn t`: run `t` in a new thread, return immediately in the current one. -/
def spawn {E : Effect.{v}} [ConcE.{v} -< E] (t : ITree E Unit) : ITree E Unit :=
  ITree.bind (Effect.trigger ConcE.{v} .fork) fun tag =>
    match tag with
    | .cur => ITree.ret ()
    | .new =>
        ITree.bind t fun _ =>
          ITree.bind (Effect.trigger ConcE.{v} .endthread) (fun o => PEmpty.elim o)

/-- `wpi_spawn`. -/
theorem wpi_spawn (t : ITree E Unit)
    (Φ : Post GF Unit) (M : CoPset) :
    iprop(Φ () ∗ wpi_mask GF H m t (fun _ => iprop(True)) ⊤)
      ⊢ wpi_mask GF H m (spawn t) Φ M := by
  simp only [spawn]
  refine .trans ?_ (wpi_fork GF _ Φ M)
  iintro ⟨HΦ, Ht⟩
  isplitl [HΦ]
  ·
    iapply wpi_ret () Φ M $$ HΦ
  ·
    iapply wpi_bind t _ (fun _ => iprop(False)) ⊤
    iapply (wpi_wand t (fun _ => iprop(True))
      (fun _ => wpi_mask GF H m _ (fun _ => iprop(False)) ⊤) ⊤) $$ [] Ht
    iintro %v Htrue
    iapply wpi_kill GF (H := H) _ _ $$ Htrue

end ConcRules

/-! ### A concrete language: pick effects, pick handlers -/

end AeneasIris.Conc
