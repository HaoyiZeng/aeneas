import AeneasIris.Effects.Heap
import AeneasIris.Effects.Step
import AeneasIris.Tactics.Triple

namespace AeneasIris.HeapAPI

open Iris BI Aeneas.Data.Coinductive
open AeneasIris AeneasIris.Heap
open Aeneas.Std (StateE StepE Loc AccessState Cell Val HMap RustHeap)
open scoped Aeneas.Std
open AeneasIris.Step (lat lat_intro stepH)

universe u

section

variable {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]
variable [G : HeapGS.{u} GF]
variable {E : Effect} [StateE RustHeap -< E] [StepE -< E]
variable {Hd : Handler E GF} [stateH heapInterp -<ₕ Hd]
variable {m : Mode} [stepH GF m -<ₕ Hd]

abbrev pointsTo (l : Loc) (dq : DFrac) {T : Type u} (v : T) : IProp GF :=
  pointsToC l dq (.reading 0) (Val.pack v)

notation:50 l:51 " ↦{" dq "} " v:51 => pointsTo l dq v
notation:50 l:51 " ↦ " v:51 => pointsTo l (DFrac.own 1) v

/-- Ownership of a cell splits along the fraction. -/
theorem pointsTo_split (l : Loc) (q₁ q₂ : Qp) {T : Type u} (v : T) :
    pointsTo (GF := GF) l (.own (q₁ + q₂)) v
      ⊣⊢ iprop(pointsTo l (.own q₁) v ∗ pointsTo l (.own q₂) v) :=
  Fractional.fractional (Φ := fun q : Qp => pointsToC l (.own q) (.reading 0) (Val.pack v))
    q₁ q₂

noncomputable def load {T : Type u} [Nonempty T] (l : Loc) : ITree E T :=
  load_at T l

def store {T : Type u} (l : Loc) (v : T) : ITree E PUnit.{u+1} :=
  store_at l (Val.pack v)

noncomputable def cas {T : Type u} (l : Loc) (old new : T) : ITree E Bool :=
  Heap.cas l (Val.pack old) (Val.pack new)

noncomputable def faa {T : Type u} [Nonempty T] [Add T] (l : Loc) (n : T) : ITree E T :=
  modify T (· + n) l

def alloc {T : Type u} (v : T) : ITree E Loc :=
  Heap.alloc (Val.pack v)

def free (l : Loc) : ITree E PUnit.{u+1} :=
  Heap.free l

theorem wpi_load {T : Type u} [Nonempty T] (l : Loc) (v : T) (dq : DFrac)
    {Φ : Post GF T} {M : CoPset} :
    lat m iprop(l ↦{dq} v ∗ (l ↦{dq} v -∗ |={M}=> Φ v))
      ⊢ wpi_mask GF Hd m (load (E := E) l) Φ M :=
  wpi_load_at (Hd := Hd) (m := m) T l 0 v dq

theorem wpi_store {T U : Type u} (l : Loc) (v : T) (w : U)
    {Φ : Post GF PUnit.{u+1}} {M : CoPset} :
    lat m iprop(l ↦ v ∗ (l ↦ w -∗ |={M}=> Φ PUnit.unit))
      ⊢ wpi_mask GF Hd m (store (E := E) l w) Φ M :=
  wpi_store_at (Hd := Hd) (m := m) l (Val.pack v) (Val.pack w)

theorem wpi_cas_succ {T : Type u} (l : Loc) (old new : T)
    {Φ : Post GF Bool} {M : CoPset} :
    lat m iprop(l ↦ old ∗ (l ↦ new -∗ |={M}=> Φ true))
      ⊢ wpi_mask GF Hd m (cas (E := E) l old new) Φ M :=
  wpi_cas_suc (Hd := Hd) (m := m) l (Val.pack old) (Val.pack new)

theorem wpi_cas_fail {T : Type u} (l : Loc) (v old new : T) (dq : DFrac) (hne : v ≠ old)
    {Φ : Post GF Bool} {M : CoPset} :
    lat m iprop(l ↦{dq} v ∗ (l ↦{dq} v -∗ |={M}=> Φ false))
      ⊢ wpi_mask GF Hd m (cas (E := E) l old new) Φ M :=
  wpi_cas_fail_of (Hd := Hd) (m := m) l 0 (Val.pack v) (Val.pack old) (Val.pack new) dq
    (fun heq => hne (eq_of_heq ((Sigma.mk.injEq .. ▸ heq).2)))

theorem wpi_cas_fail_ty {T U : Type u} (l : Loc) (v : U) (old new : T) (dq : DFrac)
    (hne : U ≠ T) {Φ : Post GF Bool} {M : CoPset} :
    lat m iprop(l ↦{dq} v ∗ (l ↦{dq} v -∗ |={M}=> Φ false))
      ⊢ wpi_mask GF Hd m (cas (E := E) l old new) Φ M :=
  wpi_cas_fail_of (Hd := Hd) (m := m) l 0 (Val.pack v) (Val.pack old) (Val.pack new) dq
    (fun heq => hne (congrArg Sigma.fst heq))

theorem wpi_faa {T : Type u} [Nonempty T] [Add T] (l : Loc) (v n : T)
    {Φ : Post GF T} {M : CoPset} :
    lat m iprop(l ↦ v ∗ (l ↦ (v + n) -∗ |={M}=> Φ v))
      ⊢ wpi_mask GF Hd m (faa (E := E) l n) Φ M :=
  wpi_modify (Hd := Hd) (m := m) T (· + n) l v

theorem wpi_alloc {T : Type u} (v : T) {Φ : Post GF Loc} {M : CoPset} :
    lat m iprop(∀ l, l ↦ v -∗ |={M}=> Φ l)
      ⊢ wpi_mask GF Hd m (alloc (E := E) v) Φ M :=
  Heap.wpi_alloc (Hd := Hd) (m := m) (Val.pack v)

theorem wpi_free {T : Type u} (l : Loc) (v : T) {Φ : Post GF PUnit.{u+1}} {M : CoPset} :
    lat m iprop(l ↦ v ∗ |={M}=> Φ PUnit.unit)
      ⊢ wpi_mask GF Hd m (free (E := E) l) Φ M :=
  Heap.wpi_free (Hd := Hd) (m := m) l (Val.pack v)

end

/-! ## Registered triples -/

section RustTriples

open Aeneas.Std (Val StepE StateE)
open AeneasIris.Heap (HeapGS heapInterp stateH)

variable {hlc : Iris.HasLC} {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]
variable [HeapGS.{0} GF]
variable {E : Effect} [StateE RustHeap.{0} -< E] [StepE -< E]
variable {Hd : Handler E GF} [stateH heapInterp.{0} -<ₕ Hd]
variable {m : Mode} [stepH GF m -<ₕ Hd]

@[istep_rule]
theorem load_body_spec {T : Type} [Nonempty T] (l : Loc) (v : T) (dq : DFrac)
    (M : CoPset) :
    ⦃ l ↦{dq} v ⦄ (Heap.load_body T l) @ Hd ; m ; M
      ⦃ r, ⌜r = v⌝ ∗ l ↦{dq} v ⦄ := by
  refine .trans ?_ (Heap.wpi_load_body (Hd := Hd) T l 0 v dq)
  iintro Hl
  isplitl [Hl]
  · iexact Hl
  · iintro Hl'
    imodintro
    isplitr [Hl']
    · itrivial
    · iexact Hl'

@[istep_rule]
theorem store_body_spec {T U : Type} (l : Loc) (v : T) (w : U) (M : CoPset) :
    ⦃ l ↦ v ⦄ (Heap.store_body l (Val.pack w)) @ Hd ; m ; M
      ⦃ _r, l ↦ w ⦄ := by
  refine .trans ?_ (Heap.wpi_store_body (Hd := Hd) l (Val.pack v) (Val.pack w))
  iintro Hl
  isplitl [Hl]
  · iexact Hl
  · iintro Hl'
    imodintro
    iexact Hl'

@[istep_rule]
theorem alloc_body_spec {T : Type} (v : T) (M : CoPset) :
    ⦃ emp ⦄ (Heap.alloc_body (Val.pack v)) @ Hd ; m ; M
      ⦃ l, l ↦ v ⦄ := by
  refine .trans ?_ (Heap.wpi_alloc_body (Hd := Hd) (Val.pack v))
  iintro _
  iintro %l Hl
  imodintro
  iexact Hl

/-- `cas`, when the compare succeeds. Tried first. -/
@[istep_rule]
theorem cas_succ_body_spec [DecidableEq Val.{0}] {T : Type} (l : Loc) (old new : T)
    (M : CoPset) :
    ⦃ l ↦ old ⦄ (Heap.cas_body l (Val.pack old) (Val.pack new)) @ Hd ; m ; M
      ⦃ r, ⌜r = true⌝ ∗ l ↦ new ⦄ := by
  refine .trans ?_ (Heap.wpi_cas_suc_body (Hd := Hd) l (Val.pack old) (Val.pack new))
  iintro Hl
  isplitl [Hl]
  · iexact Hl
  · iintro Hl'
    imodintro
    isplitr [Hl']
    · itrivial
    · iexact Hl'

/-- `cas`, when the value stored is not the one compared against. -/
@[istep_rule]
theorem cas_fail_body_spec [DecidableEq Val.{0}] {T : Type} (l : Loc) (v old new : T)
    (dq : DFrac) (hne : Val.pack v ≠ Val.pack old) (M : CoPset) :
    ⦃ l ↦{dq} v ⦄ (Heap.cas_body l (Val.pack old) (Val.pack new)) @ Hd ; m ; M
      ⦃ r, ⌜r = false⌝ ∗ l ↦{dq} v ⦄ := by
  refine .trans ?_
    (Heap.wpi_cas_fail_body (Hd := Hd) l 0 (Val.pack v) (Val.pack old) (Val.pack new) dq hne)
  iintro Hl
  isplitl [Hl]
  · iexact Hl
  · iintro Hl'
    imodintro
    isplitr [Hl']
    · itrivial
    · iexact Hl'

/-- `faa` and friends: read the old value, write `f` of it back. -/
@[istep_rule]
theorem modify_body_spec {T : Type} [Nonempty T] (f : T → T) (l : Loc) (v : T)
    (M : CoPset) :
    ⦃ l ↦ v ⦄ (Heap.modify_body T f l) @ Hd ; m ; M
      ⦃ r, ⌜r = v⌝ ∗ l ↦ (f v) ⦄ := by
  refine .trans ?_ (Heap.wpi_modify_body (Hd := Hd) T f l v)
  iintro Hl
  isplitl [Hl]
  · iexact Hl
  · iintro Hl'
    imodintro
    isplitr [Hl']
    · itrivial
    · iexact Hl'

/-- `free` gives nothing back. -/
@[istep_rule]
theorem free_body_spec {T : Type} (l : Loc) (v : T) (M : CoPset) :
    ⦃ l ↦ v ⦄ (Heap.free_body l) @ Hd ; m ; M ⦃ _r, emp ⦄ := by
  refine .trans ?_ (Heap.wpi_free_body (Hd := Hd) l (Val.pack v))
  iintro Hl
  isplitl [Hl]
  · iexact Hl
  · imodintro
    itrivial

/-! ### Reader/writer access states -/

/-- Take a read: one more reader. -/
@[istep_rule]
theorem readAcquire_body_spec (l : Loc) (n : Nat) (v : Val.{0}) (M : CoPset) :
    ⦃ l ↦[AccessState.reading n] v ⦄ (Heap.readAcquire_body l) @ Hd ; m ; M
      ⦃ r, ⌜r = v⌝ ∗ l ↦[AccessState.reading (n + 1)] v ⦄ := by
  refine .trans ?_ (Heap.wpi_readAcquire_body (Hd := Hd) l n v)
  iintro Hl
  isplitl [Hl]
  · iexact Hl
  · iintro Hl'
    imodintro
    isplitr [Hl']
    · itrivial
    · iexact Hl'

/-- Drop a read: one fewer reader. -/
@[istep_rule]
theorem readRelease_body_spec (l : Loc) (n : Nat) (v : Val.{0}) (M : CoPset) :
    ⦃ l ↦[AccessState.reading (n + 1)] v ⦄ (Heap.readRelease_body l) @ Hd ; m ; M
      ⦃ _r, l ↦[AccessState.reading n] v ⦄ := by
  refine .trans ?_ (Heap.wpi_readRelease_body (Hd := Hd) l n v)
  iintro Hl
  isplitl [Hl]
  · iexact Hl
  · iintro Hl'
    imodintro
    iexact Hl'

/-- Take the write: only from an unread cell. -/
@[istep_rule]
theorem writeAcquire_body_spec (l : Loc) (v : Val.{0}) (M : CoPset) :
    ⦃ l ↦[AccessState.reading 0] v ⦄ (Heap.writeAcquire_body l) @ Hd ; m ; M
      ⦃ _r, l ↦[AccessState.writing] v ⦄ := by
  refine .trans ?_ (Heap.wpi_writeAcquire_body (Hd := Hd) l v)
  iintro Hl
  isplitl [Hl]
  · iexact Hl
  · iintro Hl'
    imodintro
    iexact Hl'

/-- Drop the write, storing `w`. -/
@[istep_rule]
theorem writeRelease_body_spec (l : Loc) (v w : Val.{0}) (M : CoPset) :
    ⦃ l ↦[AccessState.writing] v ⦄ (Heap.writeRelease_body l w) @ Hd ; m ; M
      ⦃ _r, l ↦[AccessState.reading 0] w ⦄ := by
  refine .trans ?_ (Heap.wpi_writeRelease_body (Hd := Hd) l v w)
  iintro Hl
  isplitl [Hl]
  · iexact Hl
  · iintro Hl'
    imodintro
    iexact Hl'

/-! ### Non-atomic access -/

section NonAtomic

open AeneasIris.Step (stepH)
open Aeneas.Std (ConcE)

variable [ConcE -< E] [AeneasIris.Conc.ConcH GF -<ₕ Hd]
variable (m : Mode) [stepH GF m -<ₕ Hd]

/-- A non-atomic read. Mask `⊤`: it contains a `yield`. -/
@[istep_rule]
theorem load_na_spec (l : Loc) (n : Nat) (v : Val.{0}) :
    ⦃ l ↦[AccessState.reading n] v ⦄ (Heap.load_na l) @ Hd ; m ; ⊤
      ⦃ r, ⌜r = v⌝ ∗ l ↦[AccessState.reading n] v ⦄ := by
  refine .trans ?_ (Heap.wpi_load_na (Hd := Hd) (m := m) l n v)
  refine .trans ?_ (Step.lat_intro _ _)
  iintro Hl
  isplitl [Hl]
  · iexact Hl
  · iintro Hl'
    imodintro
    isplitr [Hl']
    · itrivial
    · iexact Hl'

/-- A non-atomic write. Mask `⊤`, for the same reason. -/
@[istep_rule]
theorem store_na_spec (l : Loc) (v w : Val.{0}) :
    ⦃ l ↦[AccessState.reading 0] v ⦄ (Heap.store_na l w) @ Hd ; m ; ⊤
      ⦃ _r, l ↦[AccessState.reading 0] w ⦄ := by
  refine .trans ?_ (Heap.wpi_store_na (Hd := Hd) (m := m) l v w)
  refine .trans ?_ (Step.lat_intro _ _)
  iintro Hl
  isplitl [Hl]
  · iexact Hl
  · iintro Hl'
    imodintro
    iexact Hl'

end NonAtomic

end RustTriples

end AeneasIris.HeapAPI
