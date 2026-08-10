import AeneasIris.Heap
import AeneasIris.Step

/-!
# The heap API

The interface a client programs against. Three things distinguish it from
`AeneasIris.Heap`:

**The access state is hidden.** `Heap` exposes `l ↦[st]{dq} v` because the
non-atomic operations move through the access states — a read is
`reading n ⇝ reading (n+1) ⇝ reading n`, a write parks the cell in `writing`
across a scheduling point. That discipline is what makes a data race a *stuck*
configuration, but a client using only atomic operations never observes it:
every operation here begins and ends at `reading 0`.

**Each operation issues a step.** Every operation is preceded by a `StepE`
event, so its rule is guarded by `lat m` — `▷` when the handler is
`stepH .later`, nothing when it is `stepH .identity`. Which one is a property of
the *handler*, so the same program supports both termination-sensitive and
termination-insensitive reasoning without restating anything. The `▷` is what
makes Löb induction available, which is what a loop or a recursive data
structure needs.

**The packing is hidden.** The heap holds `Val`, a type paired with an
inhabitant of it. That is what lets one heap carry values of different types,
but it is not what a client wants to write. `l ↦ₜ v` says the cell holds `v` at
`v`'s own type, and `loadT T l` hands back a `T`.

Each view is definitionally the one below it (`pointsTo` and `pointsToT` are
`abbrev`s), so a proof may drop a level whenever it needs to — to `Heap`'s rules
for a non-atomic access, or to the untyped rules here for an operation that does
not care what the cell holds.

## Why the typed layer restores `do`

The typed operations are not only more convenient to read: they are what makes
`do` notation usable at all.

`Val.{u}` is `(T : Type u) × T`, which lives in `Type (u+1)` — it packs a type
as data, and packing costs a universe. So an untyped operation returns a value
one level above ordinary Rust data. `do` elaborates to `Bind.bind`, whose
signature is `{α β : Type v}`: **one `do` block, one value universe**. Binding a
`load` (returning `Val.{u}`) and then returning a `Nat` crosses universes, and
`Bind.bind` cannot express it. That is why the definitions below use `ITree.bind`
explicitly — not a stylistic choice, but the only way to write them.

The typed operations project back down, so everything a client touches is at one
universe again and `do` works:

```lean
noncomputable def copy (l₁ l₂ : Loc) : ITree E Unit := do
  let a ← loadT (T := Nat) l₁
  storeT l₂ a
```

The examples at the end of this file are written that way, and their proofs are
unchanged from the `ITree.bind` versions — `Monad (ITree E)` is `ITree.bind`, so
`wpi_bind` still applies.

## Why the typed layer is not optional

`Val` has neither `DecidableEq` nor `Add`, and the two failures have different
causes.

Comparing `Val`s means comparing types, which is not decidable; the instance
exists only classically (`Aeneas.Std.Effects`), so `cas` is `noncomputable`.
That is sound — the classical instance decides the intended equality — and costs
nothing new, since `Val.unpack` is already `noncomputable`.

Adding `Val`s is worse: it would need an `Add` instance for the type held in the
cell, and `Val` carries the type but not its instances. So there is no
fetch-and-add at the untyped level at all — `Heap.modify` applies an arbitrary
function instead, and `faaT` recovers fetch-and-add by projecting first, which
puts the `Add` on `T` where it is available.
-/

namespace AeneasIris.HeapAPI

open Iris BI Aeneas.Data.Coinductive
open AeneasIris AeneasIris.Heap
open Aeneas.Std (StateE StepE Loc AccessState Cell Val HMap RustHeap)
open AeneasIris.Step (step stepP stepH lat LaterModality wpi_step wpi_stepP lat_mono lat_mono' lat_intro)

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

/-- `l ↦{dq}ₜ v`: the cell at `l` holds `v`, at `v`'s own type.

Definitionally `l ↦{dq} Val.pack v`. -/
abbrev pointsToT (l : Loc) (dq : DFrac) {T : Type u} (v : T) : IProp GF :=
  pointsTo l dq (Val.pack v)

@[inherit_doc] notation:50 l:51 " ↦{" dq "}ₜ " v:51 => pointsToT l dq v
@[inherit_doc] notation:50 l:51 " ↦ₜ " v:51 => pointsToT l (DFrac.own 1) v

/-! ## Untyped operations

Each is a `step` followed by the underlying heap event. The `step` is what the
rules turn into a `lat m`. These are the implementation; the typed operations
below are the interface.

`stepP` rather than `step`: the two differ only in the universe of the unit they
return, and `stepP`'s is polymorphic, so it can be raised to whatever the rest
of the block needs. That is what keeps these definitions in `do` notation even
when they carry a `Val.{u}`, which lives in `Type (u+1)`. -/

/-- Atomic read. -/
def load (l : Loc) : ITree E Val.{u} := do
  let _ ← stepP
  load_at l

/-- Atomic write. -/
def store (l : Loc) (v : Val.{u}) : ITree E Unit := do
  let _ ← stepP
  store_at l v

/-- Compare-and-swap. `noncomputable` because deciding `Val` equality is. -/
noncomputable def cas (l : Loc) (old new : Val.{u}) : ITree E Bool := do
  let _ ← stepP
  Heap.cas l old new

/-- Atomic read-modify-write, returning the old value. -/
def modify (f : Val.{u} → Val.{u}) (l : Loc) : ITree E Val.{u} := do
  let _ ← stepP
  Heap.modify f l

/-- Allocation. -/
def alloc (v : Val.{u}) : ITree E Loc := do
  let _ ← stepP
  Heap.alloc v

/-- Deallocation. The type held in the cell is irrelevant, so this one has no
typed counterpart. -/
def free (l : Loc) : ITree E Unit := do
  let _ ← stepP
  Heap.free l

/-! ## Untyped rules

Each is the corresponding rule of `AeneasIris.Heap` under `lat m`. -/

/-- `wpi_load`: an atomic read needs only a fraction of the cell. -/
theorem wpi_load (l : Loc) (v : Val.{u}) (dq : DFrac) (Φ : Post GF Val.{u}) (M : CoPset) :
    lat m iprop(l ↦{dq} v ∗ (l ↦{dq} v -∗ |={M}=> Φ v))
      ⊢ wpi_mask GF Hd (load l) Φ M := by
  simp only [load]
  refine .trans ?_ (wpi_bind (H := Hd) stepP _ Φ M)
  refine .trans ?_ (wpi_stepP (E := E) (m := m) (Hd := Hd) _ M)
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
  refine .trans ?_ (wpi_bind (H := Hd) stepP _ Φ M)
  refine .trans ?_ (wpi_stepP (E := E) (m := m) (Hd := Hd) _ M)
  iintro HΦ
  iapply lat_mono m _ _ $$ [] HΦ
  iintro HΦ'
  imodintro
  iapply (Heap.wpi_store_at (Hd := Hd) l v w Φ M) $$ HΦ'

/-- `wpi_cas_succ`: the compare succeeds and the cell is updated. -/
theorem wpi_cas_succ (l : Loc) (old new : Val.{u}) (Φ : Post GF Bool) (M : CoPset) :
    lat m iprop(l ↦ old ∗ (l ↦ new -∗ |={M}=> Φ true))
      ⊢ wpi_mask GF Hd (cas l old new) Φ M := by
  simp only [cas]
  refine .trans ?_ (wpi_bind (H := Hd) stepP _ Φ M)
  refine .trans ?_ (wpi_stepP (E := E) (m := m) (Hd := Hd) _ M)
  iintro HΦ
  iapply lat_mono m _ _ $$ [] HΦ
  iintro HΦ'
  imodintro
  iapply (Heap.wpi_cas_suc (Hd := Hd) l old new Φ M) $$ HΦ'

/-- `wpi_cas_fail`: a compare-and-swap that is going to fail only reads, so — like
an atomic load — a fraction suffices. -/
theorem wpi_cas_fail (l : Loc) (v old new : Val.{u}) (dq : DFrac) (hne : v ≠ old)
    (Φ : Post GF Bool) (M : CoPset) :
    lat m iprop(l ↦{dq} v ∗ (l ↦{dq} v -∗ |={M}=> Φ false))
      ⊢ wpi_mask GF Hd (cas l old new) Φ M := by
  simp only [cas]
  refine .trans ?_ (wpi_bind (H := Hd) stepP _ Φ M)
  refine .trans ?_ (wpi_stepP (E := E) (m := m) (Hd := Hd) _ M)
  iintro HΦ
  iapply lat_mono m _ _ $$ [] HΦ
  iintro HΦ'
  imodintro
  iapply (Heap.wpi_cas_fail (Hd := Hd) l 0 v old new dq hne Φ M) $$ HΦ'

/-- `wpi_modify`: an atomic read-modify-write returns the old value. -/
theorem wpi_modify (f : Val.{u} → Val.{u}) (l : Loc) (v : Val.{u})
    (Φ : Post GF Val.{u}) (M : CoPset) :
    lat m iprop(l ↦ v ∗ (l ↦ (f v) -∗ |={M}=> Φ v))
      ⊢ wpi_mask GF Hd (modify f l) Φ M := by
  simp only [modify]
  refine .trans ?_ (wpi_bind (H := Hd) stepP _ Φ M)
  refine .trans ?_ (wpi_stepP (E := E) (m := m) (Hd := Hd) _ M)
  iintro HΦ
  iapply lat_mono m _ _ $$ [] HΦ
  iintro HΦ'
  imodintro
  iapply (Heap.wpi_modify (Hd := Hd) f l v Φ M) $$ HΦ'

/-- `wpi_alloc`: a fresh cell, at a location the client does not get to choose.

The premise quantifies over `l` because allocation picks it; what comes back is
full ownership of a cell that no one else can already hold. -/
theorem wpi_alloc (v : Val.{u}) (Φ : Post GF Loc) (M : CoPset) :
    lat m iprop(∀ l, l ↦ v -∗ |={M}=> Φ l)
      ⊢ wpi_mask GF Hd (alloc (E := E) v) Φ M := by
  simp only [alloc]
  refine .trans ?_ (wpi_bind (H := Hd) stepP _ Φ M)
  refine .trans ?_ (wpi_stepP (E := E) (m := m) (Hd := Hd) _ M)
  iintro HΦ
  iapply lat_mono m _ _ $$ [] HΦ
  iintro HΦ'
  imodintro
  iapply (Heap.wpi_alloc (Hd := Hd) v Φ M) $$ HΦ'

/-! ## Typed operations -/

/-- Atomic read at an expected type.

`T` is implicit: it is fixed by the expected type at the call site, and by the
points-to the caller owns. Where neither determines it, write `loadT (T := Nat) l`. -/
noncomputable def loadT {T : Type u} [Inhabited T] (l : Loc) : ITree E T := do
  let _ ← stepP
  load_atT T l

/-- Atomic write. The type is taken from the value, so there is nothing to
supply. -/
def storeT {T : Type u} (l : Loc) (v : T) : ITree E Unit :=
  store l (Val.pack v)

/-- Compare-and-swap at a type. The comparison is `Val`-level, so a cell holding
a *different* type fails the compare rather than being reinterpreted. -/
noncomputable def casT {T : Type u} (l : Loc) (old new : T) : ITree E Bool :=
  cas l (Val.pack old) (Val.pack new)

/-- Fetch-and-add. The projection is what puts the `Add` on `T`; there is no
untyped counterpart, because `Val` does not carry the instance.

`T` is implicit — `n` determines it. -/
noncomputable def faaT {T : Type u} [Inhabited T] [Add T] (l : Loc) (n : T) : ITree E T := do
  let _ ← stepP
  modifyT T (· + n) l

/-- Allocation of a fresh cell holding `v`. -/
def allocT {T : Type u} (v : T) : ITree E Loc :=
  alloc (Val.pack v)

/-! ## Typed rules

Each is its untyped counterpart composed with `Val.unpack_pack`. That lemma is
the only place the type index does any work, and it is why the `default` branch
of `Val.unpack` is unreachable here: the points-to fixes the cell's type. -/

/-- `wpi_loadT`: a typed read returns the value at its own type, and needs only
a fraction of the cell. -/
theorem wpi_loadT {T : Type u} [Inhabited T] (l : Loc) (v : T) (dq : DFrac)
    (Φ : Post GF T) (M : CoPset) :
    lat m iprop(l ↦{dq}ₜ v ∗ (l ↦{dq}ₜ v -∗ |={M}=> Φ v))
      ⊢ wpi_mask GF Hd (loadT (E := E) (T := T) l) Φ M := by
  simp only [loadT]
  refine .trans ?_ (wpi_bind (H := Hd) stepP _ Φ M)
  refine .trans ?_ (wpi_stepP (E := E) (m := m) (Hd := Hd) _ M)
  iintro HΦ
  iapply lat_mono m _ _ $$ [] HΦ
  iintro HΦ'
  imodintro
  iapply (Heap.wpi_load_atT (Hd := Hd) T l 0 v dq Φ M) $$ HΦ'

/-- `wpi_storeT`: a typed write needs the full fraction, and may change the type
of the cell — the new points-to is at the new value's type. -/
theorem wpi_storeT {T U : Type u} (l : Loc) (v : T) (w : U)
    (Φ : Post GF Unit) (M : CoPset) :
    lat m iprop(l ↦ₜ v ∗ (l ↦ₜ w -∗ |={M}=> Φ ()))
      ⊢ wpi_mask GF Hd (storeT (E := E) l w) Φ M := by
  simp only [storeT]
  exact wpi_store (Hd := Hd) (m := m) l (Val.pack v) (Val.pack w) Φ M

/-- `wpi_casT_succ`: the compare succeeds and the cell is updated. -/
theorem wpi_casT_succ {T : Type u} (l : Loc) (old new : T)
    (Φ : Post GF Bool) (M : CoPset) :
    lat m iprop(l ↦ₜ old ∗ (l ↦ₜ new -∗ |={M}=> Φ true))
      ⊢ wpi_mask GF Hd (casT (E := E) l old new) Φ M := by
  simp only [casT]
  exact wpi_cas_succ (Hd := Hd) (m := m) l (Val.pack old) (Val.pack new) Φ M

/-- `wpi_casT_fail`: the cell holds a different value *of the same type*, so the
compare fails and only a fraction is needed. -/
theorem wpi_casT_fail {T : Type u} (l : Loc) (v old new : T) (dq : DFrac) (hne : v ≠ old)
    (Φ : Post GF Bool) (M : CoPset) :
    lat m iprop(l ↦{dq}ₜ v ∗ (l ↦{dq}ₜ v -∗ |={M}=> Φ false))
      ⊢ wpi_mask GF Hd (casT (E := E) l old new) Φ M := by
  simp only [casT]
  refine wpi_cas_fail (Hd := Hd) (m := m) l (Val.pack v) (Val.pack old) (Val.pack new) dq ?_ Φ M
  intro heq
  exact hne (eq_of_heq ((Sigma.mk.injEq .. ▸ heq).2))

/-- `wpi_casT_fail_ty`: the cell holds a value of a *different* type, so the
compare fails whatever the values are. This is the case an untyped CAS could not
express, and the reason the comparison is `Val`-level rather than post-projection. -/
theorem wpi_casT_fail_ty {T U : Type u} (l : Loc) (v : U) (old new : T) (dq : DFrac)
    (hne : U ≠ T) (Φ : Post GF Bool) (M : CoPset) :
    lat m iprop(l ↦{dq}ₜ v ∗ (l ↦{dq}ₜ v -∗ |={M}=> Φ false))
      ⊢ wpi_mask GF Hd (casT (E := E) l old new) Φ M := by
  simp only [casT]
  refine wpi_cas_fail (Hd := Hd) (m := m) l (Val.pack v) (Val.pack old) (Val.pack new) dq ?_ Φ M
  intro heq
  exact hne (congrArg Sigma.fst heq)

/-- `wpi_faaT`: fetch-and-add returns the old value and installs the sum. -/
theorem wpi_faaT {T : Type u} [Inhabited T] [Add T] (l : Loc) (v n : T)
    (Φ : Post GF T) (M : CoPset) :
    lat m iprop(l ↦ₜ v ∗ (l ↦ₜ (v + n) -∗ |={M}=> Φ v))
      ⊢ wpi_mask GF Hd (faaT (E := E) l n) Φ M := by
  simp only [faaT]
  refine .trans ?_ (wpi_bind (H := Hd) stepP _ Φ M)
  refine .trans ?_ (wpi_stepP (E := E) (m := m) (Hd := Hd) _ M)
  iintro HΦ
  iapply lat_mono m _ _ $$ [] HΦ
  iintro HΦ'
  imodintro
  iapply (Heap.wpi_modifyT (Hd := Hd) T (· + n) l v Φ M) $$ HΦ'

/-- `wpi_allocT`: a fresh cell holding `v`, at `v`'s own type. -/
theorem wpi_allocT {T : Type u} (v : T) (Φ : Post GF Loc) (M : CoPset) :
    lat m iprop(∀ l, l ↦ₜ v -∗ |={M}=> Φ l)
      ⊢ wpi_mask GF Hd (allocT (E := E) v) Φ M := by
  simp only [allocT]
  exact wpi_alloc (Hd := Hd) (m := m) (Val.pack v) Φ M

end

/-! ## Heterogeneity

The point of a dependently typed heap: **one** heap holding values of different
types, each read back at its own. If the type index were being lost anywhere
between the points-to and the rule, `b` below would come back `default` and this
would not prove — it closes with `⟨rfl, rfl⟩`. -/

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
          (do let a ← loadT (T := Nat) l₁
              let b ← loadT (T := List Bool) l₂
              return (a, b))
          (fun p => iprop(⌜p.1 = 37 ∧ p.2 = [true, false]⌝)) M := by
  iintro ⟨H₁, H₂⟩
  iapply (wpi_bind (H := Hd) (loadT (T := Nat) l₁) _ _ M)
  iapply (wpi_loadT (Hd := Hd) (m := m) l₁ (37 : Nat) (DFrac.own 1) _ M)
  iapply (lat_intro m _)
  isplitl [H₁]
  · iexact H₁
  iintro _
  imodintro
  /- First cell read back at `Nat`. Now the second, at a completely different
     type, out of the same heap. -/
  iapply (wpi_bind (H := Hd) (loadT (T := List Bool) l₂) _ _ M)
  iapply (wpi_loadT (Hd := Hd) (m := m) l₂ ([true, false] : List Bool) (DFrac.own 1) _ M)
  iapply (lat_intro m _)
  isplitl [H₂]
  · iexact H₂
  iintro _
  imodintro
  iapply (wpi_ret' (H := Hd) _ _ M).mp
  imodintro
  ipureintro
  exact ⟨rfl, rfl⟩

/-- A compare-and-swap round trip: the successful arm installs the new value. -/
example (l : Loc) (M : CoPset) :
    iprop(l ↦ₜ (1 : Nat))
      ⊢ wpi_mask GF Hd (casT (E := E) l (1 : Nat) 2)
          (fun b => iprop(⌜b = true⌝ ∗ l ↦ₜ (2 : Nat))) M := by
  iintro Hl
  iapply (wpi_casT_succ (Hd := Hd) (m := m) l 1 2 _ M)
  iapply (lat_intro m _)
  isplitl [Hl]
  · iexact Hl
  iintro Hl'
  imodintro
  isplitr [Hl']
  · ipureintro; rfl
  iexact Hl'

/-- Fetch-and-add, the operation a reference count needs. -/
example (l : Loc) (M : CoPset) :
    iprop(l ↦ₜ (1 : Nat))
      ⊢ wpi_mask GF Hd (faaT (E := E) l (1 : Nat))
          (fun v => iprop(⌜v = 1⌝ ∗ l ↦ₜ (2 : Nat))) M := by
  iintro Hl
  iapply (wpi_faaT (Hd := Hd) (m := m) l (1 : Nat) 1 _ M)
  iapply (lat_intro m _)
  isplitl [Hl]
  · iexact Hl
  iintro Hl'
  imodintro
  isplitr [Hl']
  · ipureintro; rfl
  iexact Hl'

/-- Client code, to pin down what the typed layer buys: a `do` block mixing a
read at one type with a write at another. None of this elaborates against the
untyped operations, because `Val` sits a universe above `Nat` and `Bind.bind`
allows only one value universe per block. -/
noncomputable example (l₁ l₂ : Loc) : ITree E Unit := do
  let a ← loadT (T := Nat) l₁
  let b ← loadT (T := List Bool) l₂
  storeT l₁ (a + b.length)
  storeT l₂ (b ++ [true])

end Heterogeneity

end AeneasIris.HeapAPI
