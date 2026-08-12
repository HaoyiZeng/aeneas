import Aeneas.Std.Effects
import AeneasIris.wpi
import AeneasIris.Rules
import Iris.Instances.Lib.Invariants

namespace AeneasIris.ConcE

open Iris BI Aeneas.Data.Coinductive
open Aeneas.Std (ConcE)

universe u v
open AeneasIris

variable (GF : BundledGFunctors) [Iris.InvGS_gen hlc GF]

/-! ## Operations

Pure `ITree` definitions: no handler, no Iris. Named rather than written inline
so that other effect libraries can mention them in `do` blocks, following
`Definition yield := trigger EYield` in the Coq development
(`src/threadpool/handler.v`). -/

/-- The only point at which control may pass to another thread. -/
def yield {E : Effect.{v}} [ConcE.{v} -< E] : ITree E PUnit.{v+1} :=
  Effect.trigger ConcE.{v} .yield

/-! ## The handler

The signature is `Aeneas.Std.ConcE`, which lives on the `aeneas` side so that a
translated program can mention it without depending on Iris. Only the handler
below needs separation logic. -/

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
    · /- fork: the sequential continuation is used once, in the current thread,
      and the spawning one once here — but it is `Ψs` that is under `□`, which is
      what would let a handler spawning *several* threads use it repeatedly. -/
      simp only [ConcH.run]
      iintro Hw #Hws ⟨HΨ, HΨs⟩
      isplitl [Hw HΨ]
      · iapply Hw $$ HΨ
      · iapply Hws $$ HΨs
    · /- yield: peel the two updates, swap the continuation, put them back. -/
      simp only [ConcH.run]
      iintro Hw _ H
      imod H with H
      imodintro
      imod H with H
      imodintro
      iapply Hw $$ H
    · /- endthread: neither continuation is used — the thread is over. -/
      simp only [ConcH.run]
      iintro _ _ H
      iexact H
}
end ConcHandler

/-! ## Structural rules for the concurrency effect

These are the rules a client actually uses; they correspond to `wpi_yield`,
`wpi_kill`, `wpi_fork` and `wpi_spawn` in `src/threadpool/handler.v` of the Coq
development.

Each is stated for an arbitrary ambient effect `E` containing `ConcE`, whose
handler embeds `ConcH` — the `inH` instance, which resolves automatically for
any handler built with `⊕ₕ`. -/

section ConcRules

variable {E : Effect.{v}} {H : Handler E GF} [Sub : ConcE.{v} -< E]
variable [I : ConcH GF -<ₕ H]


/-- `wpi_yield`.

The mask must be **full**. This is what forbids stepping over a yield with an
invariant open, and is the exact analogue of the atomicity side condition on
Iris' invariant-opening rule: between two yields another thread may run, so any
invariant must have been restored. -/
theorem wpi_yield (Φ : Post GF PUnit.{v+1}) :
    iprop(Φ PUnit.unit) ⊢ wpi_mask GF H (yield (E := E)) Φ ⊤ := by
  simp only [yield]
  /- `E'` and `Sub` are pinned: left implicit, instance search fires while `E'`
  is still a metavariable and diverges. -/
  refine .trans ?_ (wpi_trigger (H := H) (E' := ConcE.{v}) (Sub := Sub)
    ConcE.I.yield Φ ⊤ (ConcH GF) (fun Ψ B => inH.embed (H₁ := ConcH GF) (H₂ := H) ConcE.I.yield Ψ B))
  /- The handler demands `🧱`, i.e. close every invariant and reopen: two nested
  mask changes, each an instance of mask introduction. -/
  have intro_mask := Iris.fupd_mask_intro_subseteq (PROP := IProp GF)
    (E1 := ⊤) (E2 := ∅) (P := iprop(Φ PUnit.unit)) Iris.Std.LawfulSet.empty_subset
  exact intro_mask.trans (BIFUpdate.mono (BIFUpdate.mono intro_mask))

/-- `wpi_kill`: ending a thread proves anything.

`endthread` never returns — its result type is `PEmpty` — so the continuation is
unreachable and the postcondition is arbitrary. The mask must be full: the
handler demands `🧾 True`, i.e. all invariants restored. -/
theorem wpi_kill (kt : ConcE.O .endthread → ITree E α)
    (Φ : Post GF α) :
    iprop(True) ⊢ wpi_mask GF H (ITree.bind (Effect.trigger ConcE .endthread) kt) Φ ⊤ := by
  refine .trans ?_ (wpi_bind (H := H) _ kt Φ ⊤)
  refine .trans ?_ (wpi_trigger (H := H) (E' := ConcE) (Sub := Sub)
    ConcE.I.endthread _ ⊤ (ConcH GF) (fun Ψ B => inH.embed (H₁ := ConcH GF) (H₂ := H) ConcE.I.endthread Ψ B))
  /- The handler ignores both continuations: it only demands `🧾 True`. -/
  exact Iris.fupd_mask_intro_subseteq (E1 := ⊤) (E2 := ∅) (P := iprop(True))
    Iris.Std.LawfulSet.empty_subset

/-- `wpi_fork`.

The spawned thread is verified at the **full** mask with postcondition `False`:
it never returns to the forking thread, so nothing may be assumed of its result,
and it may not inherit open invariants. -/
theorem wpi_fork (kt : ConcE.O .fork → ITree E α)
    (Φ : Post GF α) (M : CoPset) :
    iprop(wpi_mask GF H (kt .cur) Φ M ∗ wpi_mask GF H (kt .new) (fun _ => iprop(False)) ⊤)
      ⊢ wpi_mask GF H (ITree.bind (Effect.trigger ConcE .fork) kt) Φ M := by
  /- `trigger e >>= kt` is the `vis` node whose continuation is `kt` precomposed
  with the sub-effect's answer map. -/
  simp only [Effect.trigger, itree_vis_bind]
  refine .trans ?_ (wpi_vis (H := H) _ _ Φ M)
  /- `ITree.bind` is a `partial_fixpoint`, so `ret v >>= kt` does not reduce
  definitionally; rewrite it away explicitly. -/
  have hred : ∀ (a : E.O (Subeffect.map (E₁ := ConcE) ConcE.I.fork).1),
      ITree.bind (Pure.pure ((Subeffect.map (E₁ := ConcE) ConcE.I.fork).snd a)) kt
        = kt ((Subeffect.map (E₁ := ConcE) ConcE.I.fork).snd a) :=
    fun a => itree_ret_bind _ _
  simp only [hred]
  /- Move from `H.run` back to `ConcH.run`, which is where `fork`'s two
  continuations are named. -/
  refine .trans ?_ (BIFUpdate.mono (inH.embed (H₁ := ConcH GF) (H₂ := H) ConcE.I.fork
    (fun v => wpi_mask GF H (kt v) (fun v => iprop(|={∅, M}=> Φ v)) ∅)
    (fun v => wpi_mask GF H (kt v) (fun _ => iprop(False)) ⊤)))
  simp only [ConcH, ConcH.run]
  /- The sequential branch gives up the mask (`wpi_clear_mask`); the spawned one
  already holds ⊤ and passes through the fupd by framing. -/
  exact (BI.sep_mono_left (wpi_clear_mask (H := H) (kt ConcE.Tags.cur) Φ M).mpr).trans
    BIFUpdate.frame_right

/-- `spawn t`: run `t` in a new thread, return immediately in the current one.

This is the derived operation a client writes; `fork` is the primitive. The new
thread ends with `endthread`, which is what makes its postcondition `False`
dischargeable — it never returns. -/
/- `ITree.bind` rather than `do`: `fork` answers with `ConcE.Tags.{v}`, which is
in `Type v`, while the spawned thread is `Unit`-valued, and a `do` block admits
only one value universe. -/
def spawn {E : Effect.{v}} [ConcE.{v} -< E] (t : ITree E Unit) : ITree E Unit :=
  ITree.bind (Effect.trigger ConcE.{v} .fork) fun tag =>
    match tag with
    | .cur => ITree.ret ()
    | .new =>
        ITree.bind t fun _ =>
          ITree.bind (Effect.trigger ConcE.{v} .endthread) (fun o => PEmpty.elim o)

/-- `wpi_spawn`.

The spawned thread is verified at the full mask with the trivial postcondition:
`endthread` turns "returns nothing useful" into "returns nothing at all", so
`True` here suffices where `wpi_fork` demanded `False`. -/
theorem wpi_spawn (t : ITree E Unit)
    (Φ : Post GF Unit) (M : CoPset) :
    iprop(Φ () ∗ wpi_mask GF H t (fun _ => iprop(True)) ⊤)
      ⊢ wpi_mask GF H (spawn t) Φ M := by
  simp only [spawn]
  refine .trans ?_ (wpi_fork GF _ Φ M)
  iintro ⟨HΦ, Ht⟩
  isplitl [HΦ]
  · /- Current thread: `fork` returns `.cur` and `spawn` returns immediately. -/
    iapply wpi_ret () Φ M $$ HΦ
  · /- New thread: run `t`, then `endthread`, which discharges `False`. -/
    iapply wpi_bind t _ (fun _ => iprop(False)) ⊤
    iapply (wpi_wand t (fun _ => iprop(True))
      (fun _ => wpi_mask GF H _ (fun _ => iprop(False)) ⊤) ⊤) $$ [] Ht
    iintro %v Htrue
    iapply wpi_kill GF (H := H) _ _ $$ Htrue

end ConcRules

/-! ### A concrete language: pick effects, pick handlers

`wpi.lean` is generic in the effect signature. A language is assembled *here*,
by choosing a signature and the matching handler; adding another effect touches
nothing in the generic core. -/

-- The concrete language is `Aeneas.Std.RustEffect` / `Aeneas.Std.Result`, which
-- already carries `ConcE` as a summand. Nothing language-specific is needed here.

end AeneasIris.ConcE
