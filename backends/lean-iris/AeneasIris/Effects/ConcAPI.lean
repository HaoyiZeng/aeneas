import AeneasIris.Effects.Conc
import AeneasIris.Effects.HeapAPI
import Aeneas.Std.Primitives
import AeneasIris.Rust
import AeneasIris.Tactics.Core
import Iris.Instances.Lib.Token

/-! # A spawn/join library -/

namespace AeneasIris.ConcAPI

open Iris BI Aeneas.Data.Coinductive
open AeneasIris AeneasIris.HeapAPI AeneasIris.Heap
open Aeneas.Std (Result RustEffect Loc)

unseal Aeneas.Std.Result

section

variable {T : Type}

/-- The cell a spawned thread writes its result into. -/
abbrev Handle (_T : Type) := Loc

/-- Run `t` in a new thread; hand back the cell its result will appear in. -/
noncomputable def spawnHandle (t : Result T) : Result (Handle T) := do
  let c ← HeapAPI.alloc (none : Option T)
  let _ ← AeneasIris.Conc.spawn (do
    let v ← t
    HeapAPI.store c (some v))
  Result.ok c

/-- Wait for the thread behind `c` and return its result. -/
noncomputable def join (c : Handle T) : Result T :=
  AeneasIris.Conc.waitUntil (HeapAPI.load (T := Option T) c)

/-- Run `t₁` and `t₂` concurrently and wait for both. -/
noncomputable def par {U : Type} (t₁ : Result T) (t₂ : Result U) : Result (T × U) := do
  let c₁ ← spawnHandle t₁
  let c₂ ← spawnHandle t₂
  let v₁ ← join c₁
  let v₂ ← join c₂
  Result.ok (v₁, v₂)

end

/-! ## Specifications -/

section Spec

variable {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF] [HeapGS.{0} GF]
variable [Iris.TokenG GF]
variable {T : Type}

/-! The handler is the parameter every rule below is instantiated at. -/

variable {Hd : Handler RustEffect GF}
variable [AeneasIris.Heap.stateH AeneasIris.Heap.heapInterp.{0} -<ₕ Hd]
variable [AeneasIris.Conc.ConcH GF -<ₕ Hd]
variable (m : AeneasIris.Mode) [AeneasIris.Step.stepH GF m -<ₕ Hd]

/-! ## The concurrency primitives, as triples -/

section Primitives

open AeneasIris.Conc (yieldU sync spawn ConcH)

variable {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]
variable {E : Effect.{1}} [Aeneas.Std.ConcE.{1} -< E]
variable {Hd : Handler E GF} [ConcH GF -<ₕ Hd]

/-- Yielding costs nothing and gives nothing back. -/
@[istep_rule]
theorem yieldU_spec :
    ⦃ emp ⦄ (yieldU (E := E)) @ Hd ; m ; ⊤ ⦃ _r, emp ⦄ := by
  refine .trans ?_ (Conc.wpi_yieldU GF (H := Hd) _)
  iintro _
  itrivial

/-- A synchronisation operation: the same as running it, one yield earlier. -/
@[istep_rule cont]
theorem sync_spec {α : Type} (op : ITree E α) (Q : Post GF α) :
    ⦃ wpi_mask GF Hd m op Q ⊤ ⦄ (sync op) @ Hd ; m ; ⊤ ⦃ v, Q v ⦄ :=
  Conc.wpi_sync GF (H := Hd) op Q

/-- Spawning gives nothing back: the child never reports to the parent. -/
@[istep_rule cont]
theorem spawn_spec (t : ITree E Unit) (M : CoPset) :
    ⦃ wpi_mask GF Hd m t (fun _ => iprop(True)) ⊤ ⦄ (spawn t) @ Hd ; m ; M ⦃ _r, emp ⦄ := by
  refine .trans ?_ (Conc.wpi_spawn GF (H := Hd) t _ M)
  iintro Ht
  isplitr [Ht]
  · itrivial
  · iexact Ht

end Primitives

/-- The invariant guarding a handle's cell. -/
def spawnInv (γ : Iris.GName) (c : Handle T) (Ψ : T → IProp GF) : IProp GF :=
  iprop(∃ o : Option T, c ↦ o ∗
    (⌜o = none⌝ ∨ ∃ w, ⌜o = some w⌝ ∗ (Ψ w ∨ Iris.token γ)))

/-- The right to wait on a handle, and to collect its result once. -/
def joinHandle (N : Namespace) (c : Handle T) (Ψ : T → IProp GF) : IProp GF :=
  iprop(∃ γ, Iris.token γ ∗ Iris.inv N (spawnInv γ c Ψ))

/-- Spawning hands back a handle for the thread's postcondition. -/
theorem spawnHandle_spec (N : Namespace) (t : Result T) (Ψ : T → IProp GF) :
    ⦃ WP t @ (Hd, m) ; ⊤ ⦃ v, Ψ v ⦄ ⦄ (spawnHandle t) @ Hd ; m ; ⊤ ⦃ c, joinHandle N c Ψ ⦄ := by
  iintro Ht
  iunfold spawnHandle
  istep as ⟨c, Hc⟩
  iapply (wpi_update (H := Hd) _ _ ⊤).mp
  imod Iris.token_alloc with ⟨%γ, Hγ⟩
  imod Iris.inv_alloc N ⊤ (spawnInv γ c Ψ) $$ [Hc] with #Hinv
  · inext
    iunfold spawnInv
    iexists (none : Option T)
    isplitl [Hc]
    · iexact Hc
    · ileft; itrivial
  imodintro
  ibind
  iapply (Conc.wpi_spawn (H := Hd) _ (M := ⊤))
  isplitr [Ht]
  ·
    iret
    iunfold joinHandle
    iexists γ
    isplitl [Hγ]
    · iexact Hγ
    · iexact Hinv
  ·
    iapply (wpi_bind (H := Hd) t (fun v => HeapAPI.store c (some v)) _ ⊤)
    iapply (wpi_wand (H := Hd) t (fun v => iprop(Ψ v)) _ ⊤) $$ [] Ht
    iintro %v HΨ
    iapply (wpi_open_invariant (H := Hd) N ⊤ _ _ (spawnInv γ c Ψ)
      (fun _ _ => CoPset.mem_full)) $$ Hinv
    iintro HP
    iunfold spawnInv at HP
    icases HP with ⟨%o, Hc, Hrest⟩
    iapply (wpi_update (H := Hd) _ _ _).mp
    imod Hc with Hc
    imodintro
    istep
    isplitl [Hc HΨ]
    · iunfold spawnInv
      iexists (some v)
      inext
      isplitl [Hc]
      · iexact Hc
      · iright
        iexists v
        isplitr [HΨ]
        · itrivial
        · ileft; iexact HΨ
    · itrivial

/-- `spawnHandle_spec` at `.partial`, which is the one `istep` dispatches on. -/
@[istep_rule]
theorem spawnHandle_spec_later [AeneasIris.Step.stepH GF .part -<ₕ Hd]
    (N : Namespace) (t : Result T) (Ψ : T → IProp GF) :
    ⦃ WP t @ (Hd, Mode.part) ; ⊤ ⦃ v, Ψ v ⦄ ⦄ (spawnHandle t) @ Hd ; .part ; ⊤ ⦃ c, joinHandle N c Ψ ⦄ :=
  spawnHandle_spec .part N t Ψ

/-- Waiting yields the thread's postcondition. -/
@[istep_rule]
theorem join_spec [AeneasIris.Step.stepH GF .part -<ₕ Hd]
    (N : Namespace) (c : Handle T) (Ψ : T → IProp GF) :
    ⦃ joinHandle N c Ψ ⦄ (join c) @ Hd ; .part ; ⊤ ⦃ v, Ψ v ⦄ := by
  iintro H
  iunfold joinHandle at H
  icases H with ⟨%γ, Hγ, #Hinv⟩
  iloeb as IH
  iunfold join
  iunfold Conc.waitUntil
  iapply (wpi_bind (H := Hd) (HeapAPI.load (T := Option T) c) _ _ ⊤)
  iapply (wpi_open_invariant (H := Hd) N ⊤ _ _ (spawnInv γ c Ψ)
    (fun _ _ => CoPset.mem_full)) $$ Hinv
  iintro HP
  iunfold spawnInv at HP
  icases HP with ⟨%o, Hc, Hcond⟩
  iapply (wpi_update (H := Hd) _ _ _).mp
  imod Hc with Hc
  imodintro
  istep
  icases Hcond with (%Heq | ⟨%w, %Heq, Hor⟩) <;> subst Heq
  ·
    isplitl [Hc]
    · iunfold spawnInv
      inext
      iexists (none : Option T)
      isplitl [Hc]
      · iexact Hc
      · ileft; itrivial
    iapply (wpi_bind (H := Hd) Conc.yieldU _ _ ⊤)
    iapply (Conc.wpi_yieldU (H := Hd) _)
    istep
    iunfold join at IH
    iapply IH $$ Hγ
  ·
    icases Hor with (HΨ | Hγ')
    · isplitl [Hγ Hc]
      ·
        iunfold spawnInv
        inext
        iexists (some w)
        isplitl [Hc]
        · iexact Hc
        · iright
          iexists w
          isplitr [Hγ]
          · itrivial
          · iright; iexact Hγ
      ·
        iapply (wpi_ret (H := Hd) w (fun v => Ψ v) ⊤)
        iexact HΨ
    ·
      iexfalso
      iapply (BI.entails_wand (Iris.token_exclusive γ))
      isplitl [Hγ]
      · iexact Hγ
      · iexact Hγ'

/-- Running two threads and waiting for both.

Both handles are guarded in the caller's namespace `N`. Nothing in the conclusion
mentions a namespace, so `istep` cannot infer one and leaves it open at each rule
instance it tries; the trailing `exact N` discharge those, choosing `N` throughout. -/
theorem par_spec [AeneasIris.Step.stepH GF .part -<ₕ Hd]
    {U : Type} (N : Namespace) (t₁ : Result T) (t₂ : Result U)
    (Ψ₁ : T → IProp GF) (Ψ₂ : U → IProp GF) :
    ⦃ WP t₁ @ (Hd, Mode.part) ; ⊤ ⦃ v, Ψ₁ v ⦄ ∗ WP t₂ @ (Hd, Mode.part) ; ⊤ ⦃ v, Ψ₂ v ⦄ ⦄
      (par t₁ t₂) @ Hd ; .part ; ⊤ ⦃ vs, Ψ₁ vs.1 ∗ Ψ₂ vs.2 ⦄ := by
  iintro ⟨Ht₁, Ht₂⟩
  iunfold par
  istep with spawnHandle_spec_later as ⟨c₁, Hc₁⟩
  istep with spawnHandle_spec_later as ⟨c₂, Hc₂⟩
  istep with join_spec as ⟨v₁, Hv₁⟩
  istep with join_spec as ⟨v₂, Hv₂⟩
  iret
  isplitl [Hv₁]
  · iexact Hv₁
  · iexact Hv₂
  repeat exact N

end Spec

end AeneasIris.ConcAPI