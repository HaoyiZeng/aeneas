import AeneasIris.Heap
import AeneasIris.Step

/-!
# The heap API

The interface a client programs against. Two things distinguish it from
`AeneasIris.Heap`:

**The access state is hidden.** `Heap` exposes `l ↦[st]{dq} v` because the
non-atomic operations move through the access states — a read is
`reading n ⇝ reading (n+1) ⇝ reading n`, a write parks the cell in `writing`
across a scheduling point. That discipline is what makes a data race a *stuck*
configuration, but a client using only atomic operations never observes it:
`load`, `store`, `cas` and `faa` each begin and end at `reading 0`. So this
module writes `l ↦{dq} v`, the same shape as HeapLang's
`Iris/HeapLang/PrimitiveLaws.lean`.

**Each operation issues a step.** Every operation here is preceded by a `StepE`
event, so its rule is guarded by `lat m` — `▷` when the handler is
`stepH .later`, nothing when it is `stepH .identity`. Which one is a property of
the *handler*, so the same program supports both termination-sensitive and
termination-insensitive reasoning without restating anything. The `▷` is what
makes Löb induction available, which is what a loop or a recursive data
structure needs.

The two views are the same assertion definitionally (`pointsTo` is an `abbrev`),
so a proof may drop to `Heap`'s rules whenever a non-atomic access is needed.
-/

namespace AeneasIris.HeapAPI

open Iris BI Aeneas.Data.Coinductive
open AeneasIris AeneasIris.Heap
open Aeneas.Std (StateE StepE Loc AccessState Cell Val HMap RustHeap)
open AeneasIris.Step (step stepH lat LaterModality wpi_step lat_mono)

universe u

section

variable {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]
variable {H : Type u → Type u} [Std.LawfulFiniteMap H Loc]
variable [G : HeapGS.{u} GF]
variable {E : Effect.{u+1}} [StateE RustHeap.{u} -< E] [StepE -< E]
variable {Hd : Handler E GF} [inH (stateH heapInterp.{u}) Hd]
variable {m : LaterModality} [inH (stepH GF m) Hd]

/-! ## Assertions -/

/-- `l ↦{dq} v`: the cell at `l` holds `v` and no access is in progress.

Definitionally `l ↦[reading 0]{dq} v`. -/
abbrev pointsTo (l : Loc) (dq : DFrac) (v : Val.{u}) : IProp GF :=
  pointsToC l dq (.reading 0) v

@[inherit_doc] notation:50 l:51 " ↦{" dq "} " v:51 => pointsTo l dq v
@[inherit_doc] notation:50 l:51 " ↦ " v:51 => pointsTo l (DFrac.own 1) v

/-! ## Operations

Each is a `step` followed by the underlying heap event. The `step` is what the
rules below turn into a `lat m`. -/

/-- Atomic read. -/
def load (l : Loc) : ITree E Val.{u} :=
  ITree.bind step fun _ => load_at l

/-- Atomic write. -/
def store (l : Loc) (v : Val.{u}) : ITree E Unit :=
  ITree.bind step fun _ => store_at l v

/-- Compare-and-swap. -/
def cas [DecidableEq Val.{u}] (l : Loc) (old new : Val.{u}) : ITree E Bool :=
  ITree.bind step fun _ => Heap.cas l old new

/-- Fetch-and-add. -/
def faa [Add Val.{u}] (l : Loc) (n : Val.{u}) : ITree E Val.{u} :=
  ITree.bind step fun _ => Heap.faa l n

/-- Allocation. -/
def alloc (v : Val.{u}) : ITree E Loc :=
  ITree.bind step fun _ => Heap.alloc v

/-- Deallocation. -/
def free (l : Loc) : ITree E Unit :=
  ITree.bind step fun _ => Heap.free l

/-! ## Rules

Each is the corresponding rule of `AeneasIris.Heap` under `lat m`. -/

/-- `wpi_load`: an atomic read needs only a fraction of the cell. -/
theorem wpi_load (l : Loc) (v : Val.{u}) (dq : DFrac) (Φ : Post GF Val.{u}) (M : CoPset) :
    lat m iprop(l ↦{dq} v ∗ (l ↦{dq} v -∗ |={M}=> Φ v))
      ⊢ wpi_mask GF Hd (load l) Φ M := by
  simp only [load]
  refine .trans ?_ (wpi_bind (H := Hd) step _ Φ M)
  refine .trans ?_ (wpi_step (E := E) (m := m) (Hd := Hd) _ M)
  iintro HΦ
  iapply lat_mono m _ _ $$ [] HΦ
  iintro HΦ'
  imodintro
  iapply (Heap.wpi_load_at (Hd := Hd) l 0 v dq Φ M) $$ HΦ'

/-- `wpi_store`: an atomic write needs the full fraction, which is what rules
out a concurrent accessor. -/
theorem wpi_store (l : Loc) (v w : Val.{u}) (Φ : Post GF Unit) (M : CoPset) :
    lat m iprop(l ↦ v ∗ (l ↦ w -∗ |={M}=> Φ ()))
      ⊢ wpi_mask GF Hd (store l w) Φ M := by
  simp only [store]
  refine .trans ?_ (wpi_bind (H := Hd) step _ Φ M)
  refine .trans ?_ (wpi_step (E := E) (m := m) (Hd := Hd) _ M)
  iintro HΦ
  iapply lat_mono m _ _ $$ [] HΦ
  iintro HΦ'
  imodintro
  iapply (Heap.wpi_store_at (Hd := Hd) l v w Φ M) $$ HΦ'

/-- `wpi_cas_succ`: the compare succeeds and the cell is updated. -/
theorem wpi_cas_succ [DecidableEq Val.{u}] (l : Loc) (old new : Val.{u})
    (Φ : Post GF Bool) (M : CoPset) :
    lat m iprop(l ↦ old ∗ (l ↦ new -∗ |={M}=> Φ true))
      ⊢ wpi_mask GF Hd (cas l old new) Φ M := by
  simp only [cas]
  refine .trans ?_ (wpi_bind (H := Hd) step _ Φ M)
  refine .trans ?_ (wpi_step (E := E) (m := m) (Hd := Hd) _ M)
  iintro HΦ
  iapply lat_mono m _ _ $$ [] HΦ
  iintro HΦ'
  imodintro
  iapply (Heap.wpi_cas_suc (Hd := Hd) l old new Φ M) $$ HΦ'

/-- `wpi_faa`: fetch-and-add returns the old value and installs the sum. -/
theorem wpi_faa [Add Val.{u}] (l : Loc) (v n : Val.{u}) (Φ : Post GF Val.{u}) (M : CoPset) :
    lat m iprop(l ↦ v ∗ (l ↦ (v + n) -∗ |={M}=> Φ v))
      ⊢ wpi_mask GF Hd (faa l n) Φ M := by
  simp only [faa]
  refine .trans ?_ (wpi_bind (H := Hd) step _ Φ M)
  refine .trans ?_ (wpi_step (E := E) (m := m) (Hd := Hd) _ M)
  iintro HΦ
  iapply lat_mono m _ _ $$ [] HΦ
  iintro HΦ'
  imodintro
  iapply (Heap.wpi_faa (Hd := Hd) l v n Φ M) $$ HΦ'

/-- `wpi_alloc`: a fresh cell, at a location the client does not get to choose.

The premise quantifies over `l` because allocation picks it; what comes back is
full ownership of a cell that no one else can already hold. -/
theorem wpi_alloc (v : Val.{u}) (Φ : Post GF Loc) (M : CoPset) :
    lat m iprop(∀ l, l ↦ v -∗ |={M}=> Φ l)
      ⊢ wpi_mask GF Hd (alloc (E := E) v) Φ M := by
  simp only [alloc]
  refine .trans ?_ (wpi_bind (H := Hd) step _ Φ M)
  refine .trans ?_ (wpi_step (E := E) (m := m) (Hd := Hd) _ M)
  iintro HΦ
  iapply lat_mono m _ _ $$ [] HΦ
  iintro HΦ'
  imodintro
  iapply (Heap.wpi_alloc (Hd := Hd) v Φ M) $$ HΦ'

end

end AeneasIris.HeapAPI
