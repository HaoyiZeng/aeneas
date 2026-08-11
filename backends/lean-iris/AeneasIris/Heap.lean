import Aeneas.Std.Effects
import AeneasIris.wpi
import AeneasIris.Rules
import AeneasIris.Concurrency
import AeneasIris.Step
import Iris.Instances.Lib.Invariants
import Iris.BI.Lib.GenHeap

namespace AeneasIris.Heap

open Iris BI Aeneas.Data.Coinductive
open Aeneas.Std (StateE ConcE StepE Loc AccessState Cell Val HMap RustHeap)
open scoped Aeneas.Std
open AeneasIris AeneasIris.ConcE
open AeneasIris.ConcE (yield)
open AeneasIris.Step (step stepP stepH lat lat_mono lat_mono' lat_intro wpi_stepThen LaterModality)

universe u

section StateHandler

variable {S : Type u} {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]

abbrev StateInterp (S : Type u) (GF : BundledGFunctors) := S → IProp GF

variable (SI : StateInterp S GF)

def stateH.run (i : (StateE S).I) (Ψ _Ψs : (StateE S).O i → IProp GF) : IProp GF :=
  match i with
  | .modify f => iprop%
      ∀ s, SI s ={∅}=∗ ∃ s', ⌜f s = some s'⌝ ∗ SI s' ∗ Ψ s

def stateH : Handler (StateE S) GF where
  run := stateH.run SI
  mono := by
    intro i Ψ Ψ' Ψs Ψs'
    cases i
    simp only [stateH.run]
    iintro Hw _ H %s Hsi
    imod H $$ %s Hsi with ⟨%s', Hf, Hsi', HΨ⟩
    imodintro
    iexists s'
    iframe Hf Hsi'
    iapply Hw $$ HΨ

end StateHandler

section StateOps

variable {S : Type u} {E : Effect.{u}} [StateE S -< E]

def act (f : S → Option S) : ITree E S :=
  Effect.trigger (StateE S) (.modify f)

def act' {R : Type _} (f : S → Option S) (k : S → R) : ITree E R :=
  ITree.bind (act f) fun s => ITree.ret (k s)

end StateOps

instance : Std.UnboundedHeap HMap.{u} Loc where
  notFull _ := True
  fresh {V m} _ := (m.maxKey?.getD 0) + 1
  get?_fresh {V m _} := by
    rcases h : Std.get? m ((m.maxKey?.getD 0) + 1) with _ | v
    · rfl
    · exfalso
      have hmem : ((m.maxKey?.getD 0) + 1) ∈ m :=
        Std.ExtTreeMap.isSome_getElem?_iff_mem.mp
          (by show (Std.get? m _).isSome = true; rw [h]; rfl)
      rcases hmk : m.maxKey? with _ | km
      · rw [Std.ExtTreeMap.maxKey?_eq_none_iff.mp hmk] at hmem
        exact (Std.ExtTreeMap.eq_empty_iff_forall_not_mem.mp rfl _) hmem
      · have hle := (Std.ExtTreeMap.maxKey?_eq_some_iff_getKey?_eq_self_and_forall.mp hmk).2 _ hmem
        rw [hmk] at hle
        exact absurd (Nat.isLE_compare.mp hle) (by simp)
  notFull_empty := trivial
  notFull_insert_fresh := trivial

section HeapOps

open Std.PartialMap

variable {E : Effect.{u+1}} [StateE RustHeap.{u} -< E] [ConcE -< E] [StepE -< E]

def valAt (l : Loc) (σ : RustHeap.{u}) : Val.{u} :=
  match get? σ l with
  | some (_, v) => v
  | none => default

def readAcquire (l : Loc) : ITree E Val.{u} := do
  let _ ← stepP
  act' (S := RustHeap.{u}) (fun σ =>
    match get? σ l with
    | some (.reading n, v) => some (insert σ l (.reading (n + 1), v))
    | _ => none) (valAt l)

def readRelease.{w} (l : Loc) : ITree E PUnit.{w+1} := do
  let _ ← stepP.{w, _}
  act' (S := RustHeap.{u}) (fun σ =>
    match get? σ l with
    | some (.reading (n + 1), v) => some (insert σ l (.reading n, v))
    | _ => none) (fun _ => PUnit.unit)

def writeAcquire.{w} (l : Loc) : ITree E PUnit.{w+1} := do
  let _ ← stepP.{w, _}
  act' (S := RustHeap.{u}) (fun σ =>
    match get? σ l with
    | some (.reading 0, v) => some (insert σ l (.writing, v))
    | _ => none) (fun _ => PUnit.unit)

def writeRelease.{w} (l : Loc) (v : Val.{u}) : ITree E PUnit.{w+1} := do
  let _ ← stepP.{w, _}
  act' (S := RustHeap.{u}) (fun σ =>
    match get? σ l with
    | some (.writing, _) => some (insert σ l (.reading 0, v))
    | _ => none) (fun _ => PUnit.unit)

def load_na (l : Loc) : ITree E Val.{u} := do
  let v ← readAcquire l
  let _ ← yield
  let _ ← readRelease l
  return v

def store_na (l : Loc) (v : Val.{u}) : ITree E PUnit.{u+2} := do
  let _ ← writeAcquire l
  let _ ← yield
  writeRelease l v

noncomputable def load_at (T : Type u) [Nonempty T] (l : Loc) : ITree E T := do
  let _ ← stepP
  act' (S := RustHeap.{u}) (fun σ =>
    match get? σ l with
    | some (.reading _, v) => if v.1 = T then some σ else none
    | _ => none) (fun σ => Val.unpack T (valAt l σ))

def store_at.{w} (l : Loc) (v : Val.{u}) : ITree E PUnit.{w+1} := do
  let _ ← stepP.{w, _}
  act' (S := RustHeap.{u}) (fun σ =>
    match get? σ l with
    | some (.reading 0, _) => some (insert σ l (.reading 0, v))
    | _ => none) (fun _ => PUnit.unit)

noncomputable def cas (l : Loc) (old new : Val.{u}) : ITree E Bool := do
  let _ ← stepP
  act' (S := RustHeap.{u}) (fun σ =>
    match get? σ l with
    | some (.reading 0, v) =>
        some (if v = old then insert σ l (.reading 0, new) else σ)
    | some (.reading (_ + 1), v) =>
        if v = old then none else some σ
    | _ => none)
    (fun σ => match get? σ l with
      | some (_, v) => v = old
      | none => false)

noncomputable def modify (T : Type u) [Nonempty T] (f : T → T) (l : Loc) : ITree E T := do
  let _ ← stepP
  act' (S := RustHeap.{u}) (fun σ =>
    match get? σ l with
    | some (.reading 0, v) =>
        if v.1 = T then some (insert σ l (.reading 0, Val.pack (f (Val.unpack T v)))) else none
    | _ => none) (fun σ => Val.unpack T (valAt l σ))

def alloc (v : Val.{u}) : ITree E Loc := do
  let _ ← stepP
  act' (S := RustHeap.{u})
    (fun σ => some (insert σ (Std.fresh (M := HMap.{u+1}) (K := Loc) (V := Cell.{u+1} Val.{u}) (m := σ) trivial) (.reading 0, v)))
    (fun σ => Std.fresh (M := HMap.{u+1}) (K := Loc) (V := Cell.{u+1} Val.{u}) (m := σ) trivial)

def free.{w} (l : Loc) : ITree E PUnit.{w+1} := do
  let _ ← stepP.{w, _}
  act' (S := RustHeap.{u}) (fun σ =>
    match get? σ l with
    | some (.reading 0, _) => some (delete σ l)
    | _ => none) (fun _ => PUnit.unit)

end HeapOps

section DVal
universe v
def Val.Is (d : Val.{v}) {T : Type v} (x : T) : Prop := d = Val.pack x

@[simp] theorem Val.Is_pack {T : Type v} (x : T) : Val.Is (Val.pack x) x := rfl

theorem Val.eq_of_Is {T : Type v} {x y : T} (h : Val.Is (Val.pack x) y) : x = y :=
  eq_of_heq (Sigma.mk.inj h).2
end DVal

section Act

variable {S : Type u} {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]
variable {SI : StateInterp S GF}
variable {E : Effect.{u}} [StateE S -< E]
variable {Hd : Handler E GF} [stateH SI -<ₕ Hd]

theorem wpi_act (f : S → Option S) (Φ : Post GF S) (M : CoPset) :
    iprop(|={M, ∅}=> ∀ s, SI s ={∅}=∗
        ∃ s', ⌜f s = some s'⌝ ∗ SI s' ∗ |={∅, M}=> Φ s)
      ⊢ wpi_mask GF Hd (act (S := S) f) Φ M :=
  wpi_trigger' (H' := stateH SI) (.modify f) Φ M

theorem wpi_act' {R : Type _} (f : S → Option S) (k : S → R) (Φ : Post GF R) (M : CoPset) :
    iprop(|={M, ∅}=> ∀ s, SI s ={∅}=∗
        ∃ s', ⌜f s = some s'⌝ ∗ SI s' ∗ |={∅, M}=> Φ (k s))
      ⊢ wpi_mask GF Hd (act' (S := S) f k) Φ M := by
  simp only [act']
  refine .trans ?_ (wpi_bind (H := Hd) (act f) (fun s => ITree.ret (k s)) Φ M)
  refine .trans ?_
    (wpi_act (SI := SI) f (fun s => wpi_mask GF Hd (ITree.ret (k s)) Φ M) M)
  iintro HH
  imod HH with HH
  imodintro
  iintro %s Hsi
  imod HH $$ %s Hsi with ⟨%s', Hf, Hsi', HΦ⟩
  imodintro
  iexists s'
  iframe Hf Hsi'
  imod HΦ with HΦ
  imodintro
  iapply (wpi_ret (H := Hd) (k s) Φ M)
  iexact HΦ

end Act

section HeapGhost

variable {H : Type u → Type u} [Std.LawfulFiniteMap H Loc]
variable {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]

class HeapGS (GF : BundledGFunctors) where
  ghost : GhostMapG GF Loc (Cell Val.{u}) HMap
  name : GName

attribute [reducible, instance] HeapGS.ghost

variable [G : HeapGS.{u} GF]

def heapInterp : StateInterp RustHeap.{u} GF :=
  fun σ => ghost_map_auth G.name (DFrac.own 1) σ

def pointsToC (l : Loc) (dq : DFrac) (st : AccessState) (v : Val.{u}) : IProp GF :=
  ghost_map_elem (H := HMap) G.name dq l (st, v)

notation:50 l:51 " ↦[" st "]{" dq "} " v:51 => pointsToC l dq st v
notation:50 l:51 " ↦[" st "] " v:51 => pointsToC l (DFrac.own 1) st v

instance (l : Loc) (dq : DFrac) (st : AccessState) (v : Val.{u}) :
    Timeless (PROP := IProp GF) (pointsToC l dq st v) := by
  unfold pointsToC; infer_instance

instance (l : Loc) (st : AccessState) (v : Val.{u}) :
    Persistent (PROP := IProp GF) (pointsToC l .discard st v) := by
  unfold pointsToC; infer_instance

instance (l : Loc) (st : AccessState) (v : Val.{u}) :
    Fractional (PROP := IProp GF) (fun q : Qp => pointsToC l (.own q) st v) := by
  unfold pointsToC; infer_instance

theorem pointsToC_agree (l : Loc) (dq₁ dq₂ : DFrac) (st₁ st₂ : AccessState) (v₁ v₂ : Val.{u}) :
    iprop(pointsToC l dq₁ st₁ v₁ ∗ pointsToC l dq₂ st₂ v₂) ⊢@{IProp GF}
      iprop(⌜(st₁, v₁) = (st₂, v₂)⌝) := by
  unfold pointsToC
  exact ghost_map_elem_agree (GF := GF) (H := HMap) G.name l dq₁ dq₂ _ _

variable {E : Effect.{u+1}} [StateE RustHeap.{u} -< E] [StepE -< E]
variable {Hd : Handler E GF} [stateH heapInterp.{u} -<ₕ Hd]
variable {m : LaterModality} [stepH GF m -<ₕ Hd]

private theorem valAt_of_get {σ : RustHeap.{u}} {l : Loc} {st : AccessState} {v : Val.{u}}
    (h : Std.get? σ l = some (st, v)) : valAt l σ = v := by
  simp only [valAt, h]

private theorem wpi_cell_ro {R : Type _} (l : Loc) (st : AccessState) (v : Val.{u}) (dq : DFrac)
    (f : RustHeap.{u} → Option (RustHeap.{u})) (k : RustHeap.{u} → R) (r : R)
    (Φ : Post GF R) (M : CoPset)
    (hf : ∀ σ : RustHeap.{u}, Std.get? σ l = some (st, v) → f σ = some σ)
    (hk : ∀ σ : RustHeap.{u}, Std.get? σ l = some (st, v) → k σ = r) :
    iprop(l ↦[st]{dq} v ∗ (l ↦[st]{dq} v -∗ |={M}=> Φ r))
      ⊢ wpi_mask GF Hd (act' (S := RustHeap.{u}) f k) Φ M := by
  refine .trans ?_ (wpi_act' (SI := heapInterp) f k Φ M)
  iintro ⟨Hl, HΦ⟩
  iapply Iris.fupd_mask_intro (E1 := M) (E2 := ∅) Iris.Std.LawfulSet.empty_subset
  iintro Hclose %σ Hσ
  simp only [heapInterp, pointsToC]
  ihave %Hget := Iris.ghost_map_lookup $$ Hσ Hl
  imodintro
  iexists σ
  isplitr [Hσ Hl HΦ Hclose]
  · ipureintro; exact hf σ Hget
  iframe Hσ
  imod Hclose
  imod HΦ $$ Hl with HΦ
  imodintro
  simp only [hk σ Hget]
  iexact HΦ

private theorem wpi_cell_upd {R : Type _} (l : Loc) (st st' : AccessState) (v w : Val.{u})
    (f : RustHeap.{u} → Option (RustHeap.{u})) (k : RustHeap.{u} → R) (r : R)
    (Φ : Post GF R) (M : CoPset)
    (hf : ∀ σ : RustHeap.{u}, Std.get? σ l = some (st, v) →
            f σ = some (Std.insert σ l (st', w)))
    (hk : ∀ σ : RustHeap.{u}, Std.get? σ l = some (st, v) → k σ = r) :
    iprop(l ↦[st] v ∗ (l ↦[st'] w -∗ |={M}=> Φ r))
      ⊢ wpi_mask GF Hd (act' (S := RustHeap.{u}) f k) Φ M := by
  refine .trans ?_ (wpi_act' (SI := heapInterp) f k Φ M)
  iintro ⟨Hl, HΦ⟩
  iapply Iris.fupd_mask_intro (E1 := M) (E2 := ∅) Iris.Std.LawfulSet.empty_subset
  iintro Hclose %σ Hσ
  simp only [heapInterp, pointsToC]
  ihave %Hget := Iris.ghost_map_lookup $$ Hσ Hl
  imod Iris.ghost_map_update (st', w) $$ Hσ Hl with ⟨Hσ, Hl⟩
  imodintro
  iexists (Std.insert σ l (st', w))
  isplitr [Hσ Hl HΦ Hclose]
  · ipureintro; exact hf σ Hget
  iframe Hσ
  imod Hclose
  imod HΦ $$ Hl with HΦ
  imodintro
  simp only [hk σ Hget]
  iexact HΦ

theorem wpi_load_at (T : Type u) [Nonempty T] (l : Loc) (n : Nat) (v : T) (dq : DFrac)
    {Φ : Post GF T} {M : CoPset} :
    lat m iprop(l ↦[AccessState.reading n]{dq} Val.pack v ∗
      (l ↦[AccessState.reading n]{dq} Val.pack v -∗ |={M}=> Φ v))
      ⊢ wpi_mask GF Hd (load_at T l) Φ M :=
  wpi_stepThen _ _ _ (wpi_cell_ro l _ (Val.pack v) dq _ (fun σ => Val.unpack T (valAt l σ)) v Φ M
    (fun _ h => by simp only [h]; simp)
    (fun _ h => by simp only [valAt_of_get h, Val.unpack_pack]))

theorem wpi_store_at (l : Loc) (v w : Val.{u}) {Φ : Post GF PUnit.{w+1}} {M : CoPset} :
    lat m iprop(l ↦[AccessState.reading 0] v ∗
      (l ↦[AccessState.reading 0] w -∗ |={M}=> Φ PUnit.unit))
      ⊢ wpi_mask GF Hd (store_at l w) Φ M :=
  wpi_stepThen _ _ _ (wpi_cell_upd l _ _ v w _ (fun _ => PUnit.unit) PUnit.unit Φ M
    (fun _ h => by simp only [h]) (fun _ _ => rfl))

theorem wpi_readAcquire (l : Loc) (n : Nat) (v : Val.{u}) {Φ : Post GF Val.{u}} {M : CoPset} :
    lat m iprop(l ↦[AccessState.reading n] v ∗
      (l ↦[AccessState.reading (n + 1)] v -∗ |={M}=> Φ v))
      ⊢ wpi_mask GF Hd (readAcquire l) Φ M :=
  wpi_stepThen _ _ _ (wpi_cell_upd l _ _ v v _ (valAt l) v Φ M
    (fun _ h => by simp only [h]) (fun _ h => valAt_of_get h))

theorem wpi_readRelease (l : Loc) (n : Nat) (v : Val.{u}) {Φ : Post GF PUnit.{w+1}} {M : CoPset} :
    lat m iprop(l ↦[AccessState.reading (n + 1)] v ∗
      (l ↦[AccessState.reading n] v -∗ |={M}=> Φ PUnit.unit))
      ⊢ wpi_mask GF Hd (readRelease l) Φ M :=
  wpi_stepThen _ _ _ (wpi_cell_upd l _ _ v v _ (fun _ => PUnit.unit) PUnit.unit Φ M
    (fun _ h => by simp only [h]) (fun _ _ => rfl))

theorem wpi_writeAcquire (l : Loc) (v : Val.{u}) {Φ : Post GF PUnit.{w+1}} {M : CoPset} :
    lat m iprop(l ↦[AccessState.reading 0] v ∗
      (l ↦[AccessState.writing] v -∗ |={M}=> Φ PUnit.unit))
      ⊢ wpi_mask GF Hd (writeAcquire l) Φ M :=
  wpi_stepThen _ _ _ (wpi_cell_upd l _ _ v v _ (fun _ => PUnit.unit) PUnit.unit Φ M
    (fun _ h => by simp only [h]) (fun _ _ => rfl))

theorem wpi_writeRelease (l : Loc) (v w : Val.{u}) {Φ : Post GF PUnit.{w+1}} {M : CoPset} :
    lat m iprop(l ↦[AccessState.writing] v ∗
      (l ↦[AccessState.reading 0] w -∗ |={M}=> Φ PUnit.unit))
      ⊢ wpi_mask GF Hd (writeRelease l w) Φ M :=
  wpi_stepThen _ _ _ (wpi_cell_upd l _ _ v w _ (fun _ => PUnit.unit) PUnit.unit Φ M
    (fun _ h => by simp only [h]) (fun _ _ => rfl))

section NonAtomic

variable [ConcE -< E] [ConcH GF -<ₕ Hd]

theorem wpi_load_na (l : Loc) (n : Nat) (v : Val.{u}) {Φ : Post GF Val.{u}} :
    lat m iprop(l ↦[AccessState.reading n] v ∗
      (l ↦[AccessState.reading n] v -∗ |={⊤}=> Φ v))
      ⊢ wpi_mask GF Hd (load_na l) Φ ⊤ := by
  simp only [load_na]
  refine .trans ?_ (wpi_bind (H := Hd) (readAcquire l) _ Φ ⊤)
  refine .trans ?_ (wpi_readAcquire (Hd := Hd) (m := m) l n v
    (Φ := fun v' => wpi_mask GF Hd
      (ITree.bind (yield) (fun _ =>
        ITree.bind (readRelease l) (fun _ => ITree.ret v'))) Φ ⊤) (M := ⊤))
  refine lat_mono' m ?_
  iintro ⟨Hl, HΦ⟩
  iframe Hl
  iintro Hl
  imodintro
  iapply (wpi_bind (H := Hd) (yield) _ Φ ⊤)
  iapply (wpi_yield GF (H := Hd)
    (fun _ => wpi_mask GF Hd
      (ITree.bind (readRelease l) (fun _ => ITree.ret v)) Φ ⊤))
  iapply (wpi_bind (H := Hd) (readRelease l) _ Φ ⊤)
  iapply (wpi_readRelease (Hd := Hd) (m := m) l n v (M := ⊤))
  iapply (lat_intro m _)
  isplitl [Hl]
  · iexact Hl
  iintro Hl
  imodintro
  iapply (wpi_ret' (H := Hd) v Φ ⊤).mp
  iapply HΦ $$ Hl

theorem wpi_store_na (l : Loc) (v w : Val.{u}) {Φ : Post GF PUnit.{u+2}} :
    lat m iprop(l ↦[AccessState.reading 0] v ∗
      (l ↦[AccessState.reading 0] w -∗ |={⊤}=> Φ PUnit.unit))
      ⊢ wpi_mask GF Hd (store_na l w) Φ ⊤ := by
  simp only [store_na]
  refine .trans ?_ (wpi_bind (H := Hd) (writeAcquire l) _ Φ ⊤)
  refine .trans ?_ (wpi_writeAcquire (Hd := Hd) (m := m) l v
    (Φ := fun _ => wpi_mask GF Hd
      (ITree.bind (yield) (fun _ => writeRelease l w)) Φ ⊤) (M := ⊤))
  refine lat_mono' m ?_
  iintro ⟨Hl, HΦ⟩
  iframe Hl
  iintro Hl
  imodintro
  iapply (wpi_bind (H := Hd) (yield) _ Φ ⊤)
  iapply (wpi_yield GF (H := Hd)
    (fun _ => wpi_mask GF Hd (writeRelease l w) Φ ⊤))
  iapply (wpi_writeRelease (Hd := Hd) (m := m) l v w (M := ⊤))
  iapply (lat_intro m _)
  isplitl [Hl]
  · iexact Hl
  iexact HΦ

end NonAtomic

theorem wpi_cas_suc [DecidableEq Val.{u}] (l : Loc) (old new : Val.{u}) {Φ : Post GF Bool} {M : CoPset} :
    lat m iprop(l ↦[AccessState.reading 0] old ∗
      (l ↦[AccessState.reading 0] new -∗ |={M}=> Φ true))
      ⊢ wpi_mask GF Hd (cas l old new) Φ M := by
  simp only [cas]
  refine wpi_stepThen _ _ _ ?_
  exact wpi_cell_upd l _ _ old new _ _ true Φ M
    (fun _ h => by simp only [h]; simp) (fun _ h => by simp only [h]; simp)

theorem wpi_cas_fail_of [DecidableEq Val.{u}] (l : Loc) (n : Nat) (v old new : Val.{u}) (dq : DFrac)
    (hne : v ≠ old) {Φ : Post GF Bool} {M : CoPset} :
    lat m iprop(l ↦[AccessState.reading n]{dq} v ∗
      (l ↦[AccessState.reading n]{dq} v -∗ |={M}=> Φ false))
      ⊢ wpi_mask GF Hd (cas l old new) Φ M := by
  simp only [cas]
  refine wpi_stepThen _ _ _ ?_
  exact wpi_cell_ro l _ v dq _ _ false Φ M
    (fun _ h => by cases n <;> simp only [h] <;> simp [hne])
    (fun _ h => by simp only [h]; simp [hne])

theorem wpi_modify (T : Type u) [Nonempty T] (f : T → T) (l : Loc) (v : T)
    {Φ : Post GF T} {M : CoPset} :
    lat m iprop(l ↦[AccessState.reading 0] Val.pack v ∗
      (l ↦[AccessState.reading 0] Val.pack (f v) -∗ |={M}=> Φ v))
      ⊢ wpi_mask GF Hd (modify T f l) Φ M :=
  wpi_stepThen _ _ _ (wpi_cell_upd l _ _ (Val.pack v) (Val.pack (f v)) _
    (fun σ => Val.unpack T (valAt l σ)) v Φ M
    (fun _ h => by simp only [h]; simp [Val.unpack_pack])
    (fun _ h => by simp only [valAt_of_get h, Val.unpack_pack]))

theorem wpi_alloc (v : Val.{u}) {Φ : Post GF Loc} {M : CoPset} :
    lat m iprop(∀ l, l ↦[AccessState.reading 0] v -∗ |={M}=> Φ l)
      ⊢ wpi_mask GF Hd (alloc v) Φ M := by
  simp only [alloc]
  refine wpi_stepThen _ _ _ ?_
  refine .trans ?_ (wpi_act' (SI := heapInterp) _
    (fun σ => Std.fresh (M := HMap.{u+1}) (K := Loc) (V := Cell.{u+1} Val.{u}) (m := σ) trivial) Φ M)
  iintro HΦ
  iapply Iris.fupd_mask_intro (E1 := M) (E2 := ∅) Iris.Std.LawfulSet.empty_subset
  iintro Hclose %σ Hσ
  simp only [heapInterp, pointsToC]
  imod Iris.ghost_map_insert (Std.fresh (M := HMap.{u+1}) (K := Loc) (V := Cell.{u+1} Val.{u}) (m := σ) trivial) (AccessState.reading 0, v)
    (Std.get?_fresh (M := HMap.{u+1}) (K := Loc)) $$ Hσ with ⟨Hσ, Hl⟩
  imodintro
  iexists (Std.insert σ (Std.fresh (M := HMap.{u+1}) (K := Loc) (V := Cell.{u+1} Val.{u}) (m := σ) trivial) (AccessState.reading 0, v))
  isplitr [Hσ Hl HΦ Hclose]
  · ipureintro; rfl
  iframe Hσ
  imod Hclose
  imod HΦ $$ %(Std.fresh (M := HMap.{u+1}) (K := Loc) (V := Cell.{u+1} Val.{u}) (m := σ) trivial) Hl with HΦ
  imodintro
  iexact HΦ

theorem wpi_free (l : Loc) (v : Val.{u}) {Φ : Post GF PUnit.{w+1}} {M : CoPset} :
    lat m iprop(l ↦[AccessState.reading 0] v ∗ |={M}=> Φ PUnit.unit)
      ⊢ wpi_mask GF Hd (free l) Φ M := by
  simp only [free]
  refine wpi_stepThen _ _ _ ?_
  refine .trans ?_ (wpi_act' (SI := heapInterp) _ (fun _ => PUnit.unit) Φ M)
  iintro ⟨Hl, HΦ⟩
  iapply Iris.fupd_mask_intro (E1 := M) (E2 := ∅) Iris.Std.LawfulSet.empty_subset
  iintro Hclose %σ Hσ
  simp only [heapInterp, pointsToC]
  ihave %Hget := Iris.ghost_map_lookup $$ Hσ Hl
  imod Iris.ghost_map_delete l (AccessState.reading 0, v) $$ Hσ Hl with Hσ
  imodintro
  iexists (Std.delete σ l)
  isplitr [Hσ HΦ Hclose]
  · ipureintro; simp only [Hget]
  iframe Hσ
  imod Hclose
  imod HΦ with HΦ
  imodintro
  iexact HΦ

end HeapGhost

end AeneasIris.Heap
