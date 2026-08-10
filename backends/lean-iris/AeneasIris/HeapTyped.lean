import AeneasIris.HeapAPI

/-!
# The typed heap

`AeneasIris.HeapAPI` works on `Val`, the heap's own value type: a pair of a type
and an inhabitant of it. That is what lets one heap hold values of *different*
types, but it is not what a client wants to write. Storing a `Nat` and getting a
`Val` back, then projecting, is the packing showing through.

This module hides it. `l ↦ₜ v` says the cell holds `v` *at `v`'s own type*, and
`loadT T l` hands back a `T`. Everything is definitionally the untyped version
applied to `Val.pack`, so a proof can always drop back down.

**The type index is what makes this sound.** `loadT` must be total, so it takes
`[Inhabited T]` and falls back to `default` when the cell was stored at another
type. The rules never reach that branch: `l ↦ₜ v` pins the cell's type to `v`'s,
so `Val.unpack_pack` applies and the projection is the identity. The fallback is
reachable only by a client that owns no points-to for the location — which is to
say, by no client that can use these rules at all.
-/

namespace AeneasIris.HeapTyped

open Iris BI Aeneas.Data.Coinductive
open AeneasIris AeneasIris.Heap AeneasIris.HeapAPI
open Aeneas.Std (StateE StepE Loc AccessState Cell Val HMap RustHeap)
open AeneasIris.Step (step stepH lat LaterModality wpi_step lat_mono' lat_intro)

universe u

section

variable {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]
variable {H : Type u → Type u} [Std.LawfulFiniteMap H Loc]
variable [G : HeapGS.{u} GF]
variable {E : Effect.{u+1}} [StateE RustHeap.{u} -< E] [StepE -< E]
variable {Hd : Handler E GF} [inH (stateH heapInterp.{u}) Hd]
variable {m : LaterModality} [inH (stepH GF m) Hd]

/-! ## Assertions -/

/-- `l ↦{dq}ₜ v`: the cell at `l` holds `v`, at `v`'s own type.

Definitionally `l ↦{dq} Val.pack v`, so this is a *view* of the untyped
assertion rather than a new one — the two are interchangeable by `rfl`. -/
abbrev pointsToT (l : Loc) (dq : DFrac) {T : Type u} (v : T) : IProp GF :=
  pointsTo l dq (Val.pack v)

@[inherit_doc] notation:50 l:51 " ↦{" dq "}ₜ " v:51 => pointsToT l dq v
@[inherit_doc] notation:50 l:51 " ↦ₜ " v:51 => pointsToT l (DFrac.own 1) v

/-! ## Operations -/

/-- Atomic read at an expected type. -/
noncomputable def loadT (T : Type u) [Inhabited T] (l : Loc) : ITree E T :=
  ITree.bind (load (E := E) l) fun raw => ITree.ret (Val.unpack T raw)

/-- Atomic write. The type is taken from the value, so there is nothing to
supply. -/
def storeT {T : Type u} (l : Loc) (v : T) : ITree E Unit :=
  store (E := E) l (Val.pack v)

/-- Allocation of a fresh cell holding `v`. -/
def allocT {T : Type u} (v : T) : ITree E Loc :=
  HeapAPI.alloc (E := E) (Val.pack v)

/-! ## Rules

Each is its untyped counterpart composed with `Val.unpack_pack`. -/

/-- `wpi_loadT`: a typed read returns the value at its own type, and needs only
a fraction of the cell. -/
theorem wpi_loadT (T : Type u) [Inhabited T] (l : Loc) (v : T) (dq : DFrac)
    (Φ : Post GF T) (M : CoPset) :
    lat m iprop(l ↦{dq}ₜ v ∗ (l ↦{dq}ₜ v -∗ |={M}=> Φ v))
      ⊢ wpi_mask GF Hd (loadT (E := E) T l) Φ M := by
  simp only [loadT]
  refine .trans ?_ (wpi_bind (H := Hd) (load l) _ Φ M)
  refine .trans ?_ (HeapAPI.wpi_load (Hd := Hd) (m := m) l (Val.pack v) dq _ M)
  /- What the untyped rule hands back is `Φ` applied to the projection of what
     was stored. `unpack_pack` collapses that to `Φ v` — this is the only place
     the type index does any work, and the `default` branch of `unpack` is
     unreachable precisely because the points-to fixed the cell's type. -/
  simp only [Val.unpack_pack]
  exact lat_mono' m (BI.sep_mono .rfl (BI.wand_mono .rfl (BIFUpdate.mono (wpi_ret v Φ M))))

/-- `wpi_storeT`: a typed write needs the full fraction, and may change the type
of the cell — the new points-to is at the new value's type. -/
theorem wpi_storeT {T U : Type u} (l : Loc) (v : T) (w : U)
    (Φ : Post GF Unit) (M : CoPset) :
    lat m iprop(l ↦ₜ v ∗ (l ↦ₜ w -∗ |={M}=> Φ ()))
      ⊢ wpi_mask GF Hd (storeT (E := E) l w) Φ M := by
  simp only [storeT]
  exact HeapAPI.wpi_store (Hd := Hd) (m := m) l (Val.pack v) (Val.pack w) Φ M

/-- `wpi_allocT`: a fresh cell holding `v`, at `v`'s own type. -/
theorem wpi_allocT {T : Type u} (v : T) (Φ : Post GF Loc) (M : CoPset) :
    lat m iprop(∀ l, l ↦ₜ v -∗ |={M}=> Φ l)
      ⊢ wpi_mask GF Hd (allocT (E := E) v) Φ M := by
  simp only [allocT]
  exact HeapAPI.wpi_alloc (Hd := Hd) (m := m) (Val.pack v) Φ M

end

/-! ## Heterogeneity

The point of a dependently typed heap: **one** heap holding values of different
types, each read back at its own. If the type index were being lost anywhere
between the points-to and the rule, `b` below would come back `default` and this
would not prove. -/

section Heterogeneity

variable {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]
variable [G : HeapGS.{0} GF]
variable {E : Effect.{1}} [StateE RustHeap.{0} -< E] [StepE -< E]
variable {Hd : Handler E GF} [inH (stateH heapInterp.{0}) Hd]
variable {m : LaterModality} [inH (stepH GF m) Hd]

/-- Two cells at different types, both read back correctly. -/
example (l₁ l₂ : Loc) (M : CoPset) :
    iprop(l₁ ↦ₜ (37 : Nat) ∗ l₂ ↦ₜ ([true, false] : List Bool))
      ⊢ wpi_mask GF Hd
          (ITree.bind (loadT (E := E) Nat l₁) fun a =>
           ITree.bind (loadT (E := E) (List Bool) l₂) fun b =>
           ITree.ret (a, b))
          (fun p => iprop(⌜p.1 = 37 ∧ p.2 = [true, false]⌝)) M := by
  iintro ⟨H₁, H₂⟩
  iapply (wpi_bind (H := Hd) (loadT Nat l₁) _ _ M)
  iapply (wpi_loadT (Hd := Hd) (m := m) Nat l₁ 37 (DFrac.own 1) _ M)
  iapply (lat_intro m _)
  isplitl [H₁]
  · iexact H₁
  iintro _
  imodintro
  /- First cell read back at `Nat`. Now the second, at a completely different
     type, out of the same heap. -/
  iapply (wpi_bind (H := Hd) (loadT (List Bool) l₂) _ _ M)
  iapply (wpi_loadT (Hd := Hd) (m := m) (List Bool) l₂ [true, false] (DFrac.own 1) _ M)
  iapply (lat_intro m _)
  isplitl [H₂]
  · iexact H₂
  iintro _
  imodintro
  iapply (wpi_ret' (H := Hd) _ _ M).mp
  imodintro
  ipureintro
  exact ⟨rfl, rfl⟩

end Heterogeneity

end AeneasIris.HeapTyped
