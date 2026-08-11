import AeneasIris.Heap
import AeneasIris.Step

namespace AeneasIris.HeapAPI

open Iris BI Aeneas.Data.Coinductive
open AeneasIris AeneasIris.Heap
open Aeneas.Std (StateE StepE Loc AccessState Cell Val HMap RustHeap)
open scoped Aeneas.Std
open AeneasIris.Step (lat LaterModality lat_intro stepH)

universe u

section

variable {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]
variable [G : HeapGS.{u} GF]
variable {E : Effect} [StateE RustHeap -< E] [StepE -< E]
variable {Hd : Handler E GF} [stateH heapInterp -<ₕ Hd]
variable {m : LaterModality} [stepH GF m -<ₕ Hd]

abbrev pointsTo (l : Loc) (dq : DFrac) {T : Type u} (v : T) : IProp GF :=
  pointsToC l dq (.reading 0) (Val.pack v)

notation:50 l:51 " ↦{" dq "} " v:51 => pointsTo l dq v
notation:50 l:51 " ↦ " v:51 => pointsTo l (DFrac.own 1) v

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
      ⊢ wpi_mask GF Hd (load (E := E) l) Φ M :=
  wpi_load_at (Hd := Hd) (m := m) T l 0 v dq

theorem wpi_store {T U : Type u} (l : Loc) (v : T) (w : U)
    {Φ : Post GF PUnit.{u+1}} {M : CoPset} :
    lat m iprop(l ↦ v ∗ (l ↦ w -∗ |={M}=> Φ PUnit.unit))
      ⊢ wpi_mask GF Hd (store (E := E) l w) Φ M :=
  wpi_store_at (Hd := Hd) (m := m) l (Val.pack v) (Val.pack w)

theorem wpi_cas_succ {T : Type u} (l : Loc) (old new : T)
    {Φ : Post GF Bool} {M : CoPset} :
    lat m iprop(l ↦ old ∗ (l ↦ new -∗ |={M}=> Φ true))
      ⊢ wpi_mask GF Hd (cas (E := E) l old new) Φ M :=
  wpi_cas_suc (Hd := Hd) (m := m) l (Val.pack old) (Val.pack new)

theorem wpi_cas_fail {T : Type u} (l : Loc) (v old new : T) (dq : DFrac) (hne : v ≠ old)
    {Φ : Post GF Bool} {M : CoPset} :
    lat m iprop(l ↦{dq} v ∗ (l ↦{dq} v -∗ |={M}=> Φ false))
      ⊢ wpi_mask GF Hd (cas (E := E) l old new) Φ M :=
  wpi_cas_fail_of (Hd := Hd) (m := m) l 0 (Val.pack v) (Val.pack old) (Val.pack new) dq
    (fun heq => hne (eq_of_heq ((Sigma.mk.injEq .. ▸ heq).2)))

theorem wpi_cas_fail_ty {T U : Type u} (l : Loc) (v : U) (old new : T) (dq : DFrac)
    (hne : U ≠ T) {Φ : Post GF Bool} {M : CoPset} :
    lat m iprop(l ↦{dq} v ∗ (l ↦{dq} v -∗ |={M}=> Φ false))
      ⊢ wpi_mask GF Hd (cas (E := E) l old new) Φ M :=
  wpi_cas_fail_of (Hd := Hd) (m := m) l 0 (Val.pack v) (Val.pack old) (Val.pack new) dq
    (fun heq => hne (congrArg Sigma.fst heq))

theorem wpi_faa {T : Type u} [Nonempty T] [Add T] (l : Loc) (v n : T)
    {Φ : Post GF T} {M : CoPset} :
    lat m iprop(l ↦ v ∗ (l ↦ (v + n) -∗ |={M}=> Φ v))
      ⊢ wpi_mask GF Hd (faa (E := E) l n) Φ M :=
  wpi_modify (Hd := Hd) (m := m) T (· + n) l v

theorem wpi_alloc {T : Type u} (v : T) {Φ : Post GF Loc} {M : CoPset} :
    lat m iprop(∀ l, l ↦ v -∗ |={M}=> Φ l)
      ⊢ wpi_mask GF Hd (alloc (E := E) v) Φ M :=
  Heap.wpi_alloc (Hd := Hd) (m := m) (Val.pack v)

theorem wpi_free {T : Type u} (l : Loc) (v : T) {Φ : Post GF PUnit.{u+1}} {M : CoPset} :
    lat m iprop(l ↦ v ∗ |={M}=> Φ PUnit.unit)
      ⊢ wpi_mask GF Hd (free (E := E) l) Φ M :=
  Heap.wpi_free (Hd := Hd) (m := m) l (Val.pack v)

end

section Examples

variable {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF] [G : HeapGS.{0} GF]
variable {E : Effect.{1}} [StateE RustHeap.{0} -< E] [StepE.{1} -< E]
variable {Hd : Handler E GF} [stateH heapInterp.{0} -<ₕ Hd]
variable {m : LaterModality} [stepH GF m -<ₕ Hd]

example (l₁ l₂ : Loc) {M : CoPset} :
    iprop(l₁ ↦ (37 : Nat) ∗ l₂ ↦ ([true, false] : List Bool))
      ⊢ wpi_mask GF Hd
          (do let a ← load (E := E) (T := Nat) l₁
              let b ← load (E := E) (T := List Bool) l₂
              return (a, b))
          (fun p => iprop(⌜p.1 = 37 ∧ p.2 = [true, false]⌝)) M := by
  iintro ⟨H₁, H₂⟩
  iapply (wpi_bind (H := Hd) (load (T := Nat) l₁) _ _ M)
  iapply (wpi_load (Hd := Hd) (m := m) l₁ (37 : Nat) (DFrac.own 1) (M := M))
  iapply (lat_intro m _)
  isplitl [H₁]
  · iexact H₁
  iintro _
  imodintro
  iapply (wpi_bind (H := Hd) (load (T := List Bool) l₂) _ _ M)
  iapply (wpi_load (Hd := Hd) (m := m) l₂ ([true, false] : List Bool) (DFrac.own 1) (M := M))
  iapply (lat_intro m _)
  isplitl [H₂]
  · iexact H₂
  iintro _
  imodintro
  iapply (wpi_ret' (H := Hd) _ _ M).mp
  imodintro
  ipureintro
  exact ⟨rfl, rfl⟩

example (l : Loc) {M : CoPset} :
    iprop(l ↦ (1 : Nat))
      ⊢ wpi_mask GF Hd (cas (E := E) l (1 : Nat) 2)
          (fun b => iprop(⌜b = true⌝ ∗ l ↦ (2 : Nat))) M := by
  iintro Hl
  iapply (wpi_cas_succ (Hd := Hd) (m := m) l 1 2 (M := M))
  iapply (lat_intro m _)
  isplitl [Hl]
  · iexact Hl
  iintro Hl'
  imodintro
  isplitr [Hl']
  · ipureintro; rfl
  iexact Hl'

example (l : Loc) {M : CoPset} :
    iprop(l ↦ (1 : Nat))
      ⊢ wpi_mask GF Hd (faa (E := E) l (1 : Nat))
          (fun v => iprop(⌜v = 1⌝ ∗ l ↦ (2 : Nat))) M := by
  iintro Hl
  iapply (wpi_faa (Hd := Hd) (m := m) l (1 : Nat) 1 (M := M))
  iapply (lat_intro m _)
  isplitl [Hl]
  · iexact Hl
  iintro Hl'
  imodintro
  isplitr [Hl']
  · ipureintro; rfl
  iexact Hl'

noncomputable example (l₁ l₂ : Loc) : ITree E PUnit.{1} := do
  let a : Nat ← load l₁
  let b : List Bool ← load l₂
  let _ ← store l₁ (a + b.length)
  store l₂ (b ++ [true])

end Examples

end AeneasIris.HeapAPI
