import AeneasIris.Effects.HeapAPI
import AeneasIris.Effects.ConcAPI
import AeneasIris.AtomicWpi
import AeneasIris.OneShotWpi

/-! # Heap operations with an interference point

Each operation here is its `HeapAPI` counterpart preceded by a `yield`.  A thread
may only be descheduled at a `yield` (`Semantics/Machine.lean`), so a yield-free
region is atomic and interference is observable exactly at the yields.  Placing
one immediately *before* every access therefore makes interference observable
between any two consecutive accesses, which is what the Rust memory model allows
and what a plain `HeapAPI` sequence silently forbids.

The access itself stays yield-free, so each operation is still atomic and gets a
logically atomic specification.
-/

namespace AeneasIris.AtomicHeapAPI

open Iris BI Aeneas.Data.Coinductive
open AeneasIris AeneasIris.Heap AeneasIris.HeapAPI AeneasIris.AtomicWpi
open AeneasIris.OneShotWpi
open scoped AeneasIris.OneShotWpi
open Aeneas.Std (StateE StepE Loc AccessState Cell Val HMap RustHeap)
open scoped Aeneas.Std

universe u

section

variable {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]
variable [G : HeapGS.{0} GF]
variable {E : Effect.{1}} [StateE RustHeap.{0} -< E] [StepE.{1} -< E]
variable [Aeneas.Std.ConcE.{1} -< E] [Aeneas.Std.FailE.{1} -< E]
variable {Hd : Handler E GF} [stateH heapInterp.{0} -<ₕ Hd] [Conc.ConcH GF -<ₕ Hd]
variable {m : Mode} [AeneasIris.Step.stepH GF m -<ₕ Hd]

private theorem top_sdiff_empty :
    ((⊤ : CoPset) \ (∅ : CoPset)) = (⊤ : CoPset) := by simp

/-! ## The operations -/

noncomputable def load {T : Type} (l : Loc) : ITree E T :=
  Conc.sync (HeapAPI.load (E := E) l)

noncomputable def store {T : Type} (l : Loc) (v : T) : ITree E PUnit.{1} :=
  Conc.sync (HeapAPI.store (E := E) l v)

noncomputable def cas {T : Type} (l : Loc) (old new : T) : ITree E Bool :=
  Conc.sync (HeapAPI.cas (E := E) l old new)

noncomputable def faa {T : Type} [Add T] (l : Loc) (n : T) : ITree E T :=
  Conc.sync (HeapAPI.faa (E := E) l n)

/-- Deallocation synchronises: whoever frees must see every access made through
every reference that is being given up, which is the `Acquire` fence Rust's
`Arc::drop` performs before `drop_slow`.

`alloc` has no counterpart here on purpose.  A freshly allocated location is not
reachable by any other thread until it is published, so there is nothing for an
interference point to expose; use `HeapAPI.alloc`. -/
noncomputable def free (l : Loc) : ITree E PUnit.{1} :=
  Conc.sync (HeapAPI.free (E := E) l)

/-! ## Logically atomic specifications

The `yield` is taken first, at mask `⊤`, and only then is the atomic update
opened -- an invariant may not stay open across a yield.  So the resource is
sampled *after* any interference, which is exactly the guarantee a client with
the location in an invariant needs.
-/

theorem load_spec_multishot {T : Type} (l : Loc) (dq : DFrac) :
    ⊢ ⟪ ∀ v, l ↦{dq} (v : T) ⟫
        Hd m (load (E := E) (T := T) l) @ (∅ : CoPset)
      ⟪ l ↦{dq} v | r, RET r ; ⌜r = v⌝ ⟫ := by
  simp only [atomicWpi]
  iintro %Φ HAU
  simp only [load, top_sdiff_empty]
  istep
  iaupd_commit HAU as v with Hl
  istep
  iexists ()
  isplitl [Hl]
  · iexact Hl
  · iintro HΨ
    simp only [AtomicWpi.wandM_some]
    iapply HΨ $$ %v
    itrivial

/-! ## The exclusive-ownership form

Nothing is lost by stating the specs atomically: a client that simply *owns* the
location still gets an ordinary triple, since a yield cannot disturb owned
resources.  A client that shares the location gets the atomic form, which the
ordinary triple could not provide.
-/

@[istep_rule]
theorem load_triple {T : Type} (l : Loc) (v : T) (dq : DFrac) :
    ⦃ l ↦{dq} v ⦄ (load (E := E) (T := T) l) @ Hd ; m ; ⊤
      ⦃ r, ⌜r = v⌝ ∗ l ↦{dq} v ⦄ := by
  iintro Hl
  simp only [load]
  istep
  isplitr [Hl]
  · itrivial
  · iexact Hl

/-- The same guarantee as `load_spec_multishot`, stated one-shot. -/
@[istep_rule atomic]
theorem load_spec {T : Type} (l : Loc) (dq : DFrac) :
    ⟪ ∀ v, l ↦{dq} (v : T) ⟫ Hd m (load (E := E) (T := T) l) @ (∅ : CoPset)
      ⟪ l ↦{dq} v ⟫ ⦃ RET v ⦄ := by
  unfold IASpec
  iintro %Φ _ HAU
  simp only [load, top_sdiff_empty]
  istep
  iapply (AeneasIris.wpi_clear_mask (H := Hd) _ Φ ⊤).mp
  imod HAU with ⟨%v, Hl, Hclose⟩
  imodintro
  istep
  iapply Hclose $$ %() Hl
  exact ()
  itrivial

omit [Aeneas.Std.FailE -< E] in
/-- Writing: the caller hands over the cell at whatever value it holds. -/
@[istep_rule atomic]
theorem store_spec {T U : Type} (l : Loc) (w : U) :
    ⟪ ∀ v, l ↦ (v : T) ⟫ Hd m (store (E := E) l w) @ (∅ : CoPset)
      ⟪ l ↦ w ⟫ ⦃ RET PUnit.unit ⦄ := by
  unfold IASpec
  iintro %Φ _ HAU
  simp only [store, top_sdiff_empty]
  istep
  iapply (AeneasIris.wpi_clear_mask (H := Hd) _ Φ ⊤).mp
  imod HAU with ⟨%v, Hl, Hclose⟩
  imodintro
  istep as ⟨_r, Hl'⟩
  iapply Hclose $$ %() Hl'
  exact ()
  itrivial

omit [Aeneas.Std.FailE -< E] in
@[istep_rule]
theorem store_triple {T U : Type} (l : Loc) (v : T) (w : U) :
    ⦃ l ↦ v ⦄ (store (E := E) l w) @ Hd ; m ; ⊤ ⦃ _r, l ↦ w ⦄ := by
  iintro Hl
  simp only [store]
  istep as ⟨_r, Hl'⟩
  iexact Hl'

/-- Read-modify-write: the old value comes back, the new one is `+ n`. -/
@[istep_rule atomic]
theorem faa_spec {T : Type} [Add T] (l : Loc) (n : T) :
    ⟪ ∀ v, l ↦ (v : T) ⟫ Hd m (faa (E := E) l n) @ (∅ : CoPset)
      ⟪ l ↦ (v + n) ⟫ ⦃ RET v ⦄ := by
  unfold IASpec
  iintro %Φ _ HAU
  simp only [faa, top_sdiff_empty]
  istep
  iapply (AeneasIris.wpi_clear_mask (H := Hd) _ Φ ⊤).mp
  imod HAU with ⟨%v, Hl, Hclose⟩
  imodintro
  istep
  iapply Hclose $$ %() Hl
  exact ()
  itrivial

@[istep_rule]
theorem faa_triple {T : Type} [Add T] (l : Loc) (v n : T) :
    ⦃ l ↦ v ⦄ (faa (E := E) l n) @ Hd ; m ; ⊤ ⦃ r, ⌜r = v⌝ ∗ l ↦ (v + n) ⦄ := by
  iintro Hl
  simp only [faa]
  istep
  isplitr [Hl]
  · itrivial
  · iexact Hl

omit [Aeneas.Std.FailE -< E] in
@[istep_rule atomic]
theorem free_spec {T : Type} (l : Loc) :
    ⟪ ∀ v, l ↦ (v : T) ⟫ Hd m (free (E := E) l) @ (∅ : CoPset)
      ⟪ emp ⟫ ⦃ RET PUnit.unit ⦄ := by
  unfold IASpec
  iintro %Φ _ HAU
  simp only [free, top_sdiff_empty]
  istep
  iapply (AeneasIris.wpi_clear_mask (H := Hd) _ Φ ⊤).mp
  imod HAU with ⟨%v, Hl, Hclose⟩
  imodintro
  istep
  iapply Hclose $$ %() []
  · first | exact () | itrivial
  · exact ()
  · first | exact () | itrivial

omit [Aeneas.Std.FailE -< E] in
@[istep_rule]
theorem free_triple {T : Type} (l : Loc) (v : T) :
    ⦃ l ↦ v ⦄ (free (E := E) l) @ Hd ; m ; ⊤ ⦃ _r, emp ⦄ := by
  iintro Hl
  simp only [free]
  istep
  itrivial

/-! ### Compare-and-swap

`HeapAPI` states the two outcomes separately, which suits a caller that already
knows what the cell holds.  An atomic caller does not: the value is only fixed at
the linearisation point, and choosing the branch is the whole reason to run a CAS.
So the atomic form is stated once, over both outcomes.
-/

/-- `Val.pack` is a dependent pair, so at a fixed type it is injective.  Without
this the specification would have to compare *packed* values, leaking the heap's
representation into a statement its callers have to read. -/
theorem pack_inj {T : Type} {a b : T} : Val.pack a = Val.pack b ↔ a = b :=
  ⟨fun h => eq_of_heq (Sigma.mk.inj h).2, fun h => by rw [h]⟩

omit [Aeneas.Std.FailE -< E] in
@[istep_rule atomic]
theorem cas_spec [DecidableEq Val.{0}] {T : Type} [DecidableEq T]
    (l : Loc) (old new : T) :
    ⟪ ∀ v, l ↦ (v : T) ⟫ Hd m (cas (E := E) l old new) @ (∅ : CoPset)
      ⟪ if v = old then l ↦ new else l ↦ v ⟫
      ⦃ RET (decide (v = old)) ⦄ := by
  unfold IASpec
  iintro %Φ _ HAU
  simp only [cas, top_sdiff_empty]
  istep
  iapply (AeneasIris.wpi_clear_mask (H := Hd) _ Φ ⊤).mp
  imod HAU with ⟨%v, Hl, Hclose⟩
  imodintro
  by_cases h : v = old
  · simp only [h, if_pos, decide_true]
    istep as ⟨r, Hl'⟩
    iapply Hclose $$ %() Hl'
    exact ()
    itrivial
  · simp only [h, decide_false, if_false]
    istep
    · iapply Hclose $$ %() Hl
      exact ()
      itrivial
    · exact fun hp => h (pack_inj.mp hp)

omit [Aeneas.Std.FailE -< E] in
@[istep_rule]
theorem cas_succ_triple [DecidableEq Val.{0}] {T : Type} (l : Loc) (old new : T) :
    ⦃ l ↦ old ⦄ (cas (E := E) l old new) @ Hd ; m ; ⊤
      ⦃ r, ⌜r = true⌝ ∗ l ↦ new ⦄ := by
  iintro Hl
  simp only [cas]
  istep
  isplitr [Hl]
  · itrivial
  · iexact Hl

omit [Aeneas.Std.FailE -< E] in
@[istep_rule]
theorem cas_fail_triple [DecidableEq Val.{0}] {T : Type} (l : Loc) (v old new : T)
    (dq : DFrac) (hne : Val.pack v ≠ Val.pack old) :
    ⦃ l ↦{dq} v ⦄ (cas (E := E) l old new) @ Hd ; m ; ⊤
      ⦃ r, ⌜r = false⌝ ∗ l ↦{dq} v ⦄ := by
  iintro Hl
  simp only [cas]
  istep
  · isplitr [Hl]
    · itrivial
    · iexact Hl
  · exact hne

end

end AeneasIris.AtomicHeapAPI
