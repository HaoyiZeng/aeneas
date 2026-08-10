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
open AeneasIris AeneasIris.ConcE
open AeneasIris.ConcE (yield)
open AeneasIris.Step (stepH lat)

universe u

/-! ## The state effect

The signature is `Aeneas.Std.StateE`, defined next to `RustEffect` so that a
translated program can mention it without depending on Iris. Only the handler
below needs separation logic. -/

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

/-! ## Running a state event

`act f` is one `modify`. Note `stateH` hands the continuation the state as it
was **before** the update: that is what lets `cas` and `faa` compute their
result from a single event.

`act'` post-composes a pure read-off. It is spelled with `ITree.bind` rather
than `do` on purpose: `Monad (ITree.{u} E)` fixes a *single* value universe for
a whole `do` block, whereas here the state lives in `Type u` and the result in
some unrelated `Type v` (`Unit`, `Bool`, `Loc`, …). `ITree.bind` is
universe-heterogeneous, so it accommodates both. -/

section StateOps

variable {S : Type u} {E : Effect.{u}} [StateE S -< E]

def act (f : S → Option S) : ITree E S :=
  Effect.trigger (StateE S) (.modify f)

def act' {R : Type _} (f : S → Option S) (k : S → R) : ITree E R :=
  ITree.bind (act f) fun s => ITree.ret (k s)

end StateOps


/-! The heap's *types* — `Loc`, `AccessState`, `Cell`, `Val`, `RustHeap` — live
in `Aeneas.Std.Effects`, because `RustEffect` mentions them. What follows is
everything that needs Iris: the operations, the handler and the rules. -/


/-! ## Allocation

`iris-lean` states allocation abstractly (`Iris/Std/PartialMap.lean:79-89`): a
`Heap` supplies `fresh` given a proof that the map is `notFull`, and an
`UnboundedHeap` adds that the empty map is not full and stays so after
inserting at a fresh key. Nothing here needs to compute an address; `alloc`
just uses `fresh`.

The instance was previously missing — `(K → Option ·)` is a `Heap` but not
finite, `ExtTreeMap` is finite but had no `Heap` — so this file computed
addresses by hand. Now that the heap is fixed to `HMap`, the instance can be
supplied once and the hand-rolled allocator deleted. `Loc = Nat` has no upper
bound, so `notFull` is trivially true, and `fresh` is one past `ExtTreeMap`'s
own `maxKey?` — the container is ordered, so that is O(log n) and its
correctness follows from `maxKey?_eq_some_iff_getKey?_eq_self_and_forall`. -/

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


variable {E : Effect.{u+1}} [StateE RustHeap.{u} -< E] [ConcE -< E]

/-- Read off the value at `l`, or `default` if it is absent. -/
def valAt (l : Loc) (σ : RustHeap.{u}) : Val.{u} :=
  match get? σ l with
  | some (_, v) => v
  | none => default

/-! ### Correspondence with λRust

The access-state guards below are exactly those of λRust's `base_step`
(`lambda-rust/lang/lang.v`), whose state is `gmap loc (lock_state * val)` with
`lock_state ::= WSt | RSt n`:

| λRust rule    | requires        | produces           | ours            |
|---------------|-----------------|--------------------|-----------------|
| `ReadScS`     | `RSt n`, any n  | unchanged          | `load_at`       |
| `ReadNa1S`    | `RSt n`         | `RSt (S n)`        | `readAcquire`   |
| `ReadNa2S`    | `RSt (S n)`     | `RSt n`            | `readRelease`   |
| `WriteScS`    | `RSt 0`         | `RSt 0`, new value | `store_at`      |
| `WriteNa1S`   | `RSt 0`         | `WSt`              | `writeAcquire`  |
| `WriteNa2S`   | `WSt`           | `RSt 0`, new value | `writeRelease`  |
| `CasFailS`    | `RSt n`, any n  | unchanged          | `cas`, fail arm |
| `CasSucS`     | `RSt 0`         | `RSt 0`, new value | `cas`, succ arm |
| `CasStuckS`   | `RSt n`, `0<n`  | **stuck**          | `cas`, `none`   |

A race is a state in which no rule applies — the program is *stuck*. Since a
weakest precondition implies progress, proving one proves race-freedom; that is
λRust's `safe_nonracing` (`lambda-rust/lang/races.v`), and it is why the
*specifications* for atomic and non-atomic access are identical there. Races are
ruled out by ownership (a write needs the full fraction), not by anything in the
specification.

Note that `load_at` accepts `reading n` for **any** `n`: an atomic read may
proceed while non-atomic reads are in flight, since read/read never races. -/

/-- Begin a non-atomic read: `reading n ⇝ reading (n+1)`; UB while a write is in
progress, or if the location is dangling. -/
def readAcquire (l : Loc) : ITree E Val.{u} :=
  act' (S := RustHeap.{u}) (fun σ =>
    match get? σ l with
    | some (.reading n, v) => some (insert σ l (.reading (n + 1), v))
    | _ => none) (valAt l)

/-- End a non-atomic read: `reading (n+1) ⇝ reading n`. -/
def readRelease (l : Loc) : ITree E Unit :=
  act' (S := RustHeap.{u}) (fun σ =>
    match get? σ l with
    | some (.reading (n + 1), v) => some (insert σ l (.reading n, v))
    | _ => none) (fun _ => ())

/-- Begin a non-atomic write: `reading 0 ⇝ writing`; UB if any other access is in
progress. -/
def writeAcquire (l : Loc) : ITree E Unit :=
  act' (S := RustHeap.{u}) (fun σ =>
    match get? σ l with
    | some (.reading 0, v) => some (insert σ l (.writing, v))
    | _ => none) (fun _ => ())

/-- End a non-atomic write, storing `v`: `writing ⇝ reading 0`. -/
def writeRelease (l : Loc) (v : Val.{u}) : ITree E Unit :=
  act' (S := RustHeap.{u}) (fun σ =>
    match get? σ l with
    | some (.writing, _) => some (insert σ l (.reading 0, v))
    | _ => none) (fun _ => ())

/-! ### Non-atomic accesses: two phases, with a yield between them

λRust's non-atomic accesses are two *reduction steps* of the operational
semantics: `Read Na1Ord l` steps to `Read Na2Ord l` (`ReadNa1S`), and only the
second step produces the value (`ReadNa2S`); likewise `WriteNa1S` marks the cell
`WSt` while leaving the **old** value, and `WriteNa2S` installs the new one. In
Iris' thread-pool semantics every reduction step is a scheduling point, so the
intermediate state is observable by other threads — and that is the whole point:
a concurrent `ReadScS` (which needs `RSt n`) or `WriteNa1S` (which needs
`RSt 0`) finds no applicable rule and the program is *stuck*, which is how
λRust reports a data race (`safe_nonracing`, `lang/races.v`).

Our scheduler switches threads **only** at `ConcE.yield` — every other event
runs to completion in the current thread (`src/threadpool/scheduler.v`: the
non-threadpool case keeps `tid` fixed). So the two phases must be separated by
an explicit `yield`, or no other thread could ever observe the intermediate
state and the access-state guards below would be unreachable.

The yield is what makes these operations genuinely non-atomic, and it is why
their specifications require the full mask: no invariant may be held open across
a non-atomic access. -/

/-- Non-atomic read: acquire, yield, release.

Explicit `ITree.bind` rather than `do`: `Monad (ITree E)` fixes one value
universe for a whole `do` block, and this one mixes a `V`-valued read with
`Unit`-valued steps. `ITree.bind` has no such restriction. -/
def load_na (l : Loc) : ITree E Val.{u} :=
  ITree.bind (readAcquire l) fun v =>
    ITree.bind yield fun _ =>
      ITree.bind (readRelease l) fun _ => ITree.ret v

/-- Non-atomic write: acquire, yield, release storing `v`. -/
def store_na (l : Loc) (v : Val.{u}) : ITree E Unit := do
  let _ ← writeAcquire l
  let _ ← yield
  writeRelease l v

/-! ### Atomic accesses

Single events, and — unlike the non-atomic operations — genuinely instantaneous:
there is no window at all, not merely no yield. Each requires the cell to be
idle, which is how mixing atomic and non-atomic access to one location is
reported as a race. -/

def load_at (l : Loc) : ITree E Val.{u} :=
  act' (S := RustHeap.{u}) (fun σ =>
    match get? σ l with
    | some (.reading _, _) => some σ
    | _ => none) (valAt l)

/-- Atomic read, projected at an expected type.

Not `load_at` followed by a projection: `act'` post-composes a pure read-off, so
folding `Val.unpack` into that read-off costs nothing and keeps the result in
`Type u`. That is what lets the API layer stay in `do` notation — a `Val` would
have dragged the whole block up a universe. -/
noncomputable def load_atT (T : Type u) [Inhabited T] (l : Loc) : ITree E T :=
  act' (S := RustHeap.{u}) (fun σ =>
    match get? σ l with
    | some (.reading _, _) => some σ
    | _ => none) (fun σ => Val.unpack T (valAt l σ))

def store_at (l : Loc) (v : Val.{u}) : ITree E Unit :=
  act' (S := RustHeap.{u}) (fun σ =>
    match get? σ l with
    | some (.reading 0, _) => some (insert σ l (.reading 0, v))
    | _ => none) (fun _ => ())

/-- Compare-and-swap. A read-modify-write, so exactly one `modify`; the old
state comes back, which is what lets the result be computed without a second
event.

The guard mirrors λRust's three CAS rules exactly, and the asymmetry is
deliberate:

* `CasFailS` accepts `RSt n` for *any* `n` — a CAS that is going to fail only
  reads, and reads never race.
* `CasSucS` demands `RSt 0` — a CAS that is going to succeed writes, so any
  concurrent non-atomic reader is a race.
* `CasStuckS` is the one place the semantics must *actively* detect a race: it
  fires when the comparison succeeds but `0 < n`, and reduces to a stuck state.
  λRust needs this explicitly because failing and succeeding CAS are not
  mutually exclusive, so one cannot rely on the state already being stuck. We
  reproduce it by returning `none` in exactly that case. -/
def cas [DecidableEq Val.{u}] (l : Loc) (old new : Val.{u}) : ITree E Bool :=
  act' (S := RustHeap.{u}) (fun σ =>
    match get? σ l with
    | some (.reading 0, v) =>
        /- Idle: both outcomes are legal. -/
        some (if v = old then insert σ l (.reading 0, new) else σ)
    | some (.reading (_ + 1), v) =>
        /- Readers in flight: failing is fine, succeeding is a race. -/
        if v = old then none else some σ
    | _ => none)
    (fun σ => match get? σ l with
      | some (_, v) => v = old
      | none => false)

/-- Atomic read-modify-write: replace the cell's contents by `f` of them and
return the *old* value. A single event, like `cas`.

This is deliberately more general than fetch-and-add, because fetch-and-add
cannot be stated here at all: adding two `Val`s would need an `Add` instance for
the type held in the cell, and `Val` carries the type but not its instances. The
typed layer recovers `faa` by projecting first, which puts the `Add` on `T`
where it is available. -/
def modify (f : Val.{u} → Val.{u}) (l : Loc) : ITree E Val.{u} :=
  act' (S := RustHeap.{u}) (fun σ =>
    match get? σ l with
    | some (.reading 0, v) => some (insert σ l (.reading 0, f v))
    | _ => none) (valAt l)

/-- Atomic read-modify-write at a type: apply `f` to the cell's contents and
return the old value. This is what makes fetch-and-add expressible — `Add` lands
on `T`, where it exists, rather than on `Val`, where it cannot. -/
noncomputable def modifyT (T : Type u) [Inhabited T] (f : T → T) (l : Loc) : ITree E T :=
  act' (S := RustHeap.{u}) (fun σ =>
    match get? σ l with
    | some (.reading 0, v) => some (insert σ l (.reading 0, Val.pack (f (Val.unpack T v))))
    | _ => none) (fun σ => Val.unpack T (valAt l σ))

/-- Allocation is a single event: no other thread can observe a half-built cell.
The location is `fresh` of the *pre*-state, which is why no freshness
argument is needed — and why `alloc` asks for nothing beyond the finite-map
structure the ghost heap already requires. -/
def alloc (v : Val.{u}) : ITree E Loc :=
  act' (S := RustHeap.{u})
    (fun σ => some (insert σ (Std.fresh (M := HMap.{u+1}) (K := Loc) (V := Cell.{u+1} Val.{u}) (m := σ) trivial) (.reading 0, v)))
    (fun σ => Std.fresh (M := HMap.{u+1}) (K := Loc) (V := Cell.{u+1} Val.{u}) (m := σ) trivial)

/-- Deallocation; UB unless the cell is idle. -/
def free (l : Loc) : ITree E Unit :=
  act' (S := RustHeap.{u}) (fun σ =>
    match get? σ l with
    | some (.reading 0, _) => some (delete σ l)
    | _ => none) (fun _ => ())

end HeapOps


/-! ## The dependent heap

`Val` and `Val.pack` are now in `Aeneas.Std.Effects`; what remains here is the
specification-level relation used to state rules. -/

section DVal
universe v
/-- `d.Is x` says `d` holds exactly `x`, at `x`'s type. No *computational*
projection is possible — type equality in `Type u` is not decidable — and none
is needed for stating rules: a points-to `l ↦ Val.pack x` already records the
type. -/
def Val.Is (d : Val.{v}) {T : Type v} (x : T) : Prop := d = Val.pack x

@[simp] theorem Val.Is_pack {T : Type v} (x : T) : Val.Is (Val.pack x) x := rfl

theorem Val.eq_of_Is {T : Type v} {x y : T} (h : Val.Is (Val.pack x) y) : x = y :=
  eq_of_heq (Sigma.mk.inj h).2
end DVal



/-! ## Triggering a sub-effect

The side condition of `wpi_trigger` is discharged by `AeneasIris.inH`, whose
instances resolve it by structure — including through nested sums, which is the
shape `RustEffect` has. `wpi_trigger'` lives in `AeneasIris.Rules`. -/

/-! ## The workhorse

`act f` is one `modify` event; `act' f k` is that event followed by a pure
read-off `k` of the **pre**-state (`stateH` hands the continuation the state as
it was before the update, which is what makes `cas` and `faa` single events). -/

section Act

variable {S : Type u} {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]
variable {SI : StateInterp S GF}
variable {E : Effect.{u}} [StateE S -< E]
variable {Hd : Handler E GF} [inH (stateH SI) Hd]

/-- Running a single `modify`: give up the state interpretation at `∅`, produce
a successor state the guard accepts, and get the pre-state back. -/
theorem wpi_act (f : S → Option S) (Φ : Post GF S) (M : CoPset) :
    iprop(|={M, ∅}=> ∀ s, SI s ={∅}=∗
        ∃ s', ⌜f s = some s'⌝ ∗ SI s' ∗ |={∅, M}=> Φ s)
      ⊢ wpi_mask GF Hd (act (S := S) f) Φ M :=
  wpi_trigger' (H' := stateH SI) (.modify f) Φ M

/-- The shape every heap operation has. -/
theorem wpi_act' {R : Type _} (f : S → Option S) (k : S → R) (Φ : Post GF R) (M : CoPset) :
    iprop(|={M, ∅}=> ∀ s, SI s ={∅}=∗
        ∃ s', ⌜f s = some s'⌝ ∗ SI s' ∗ |={∅, M}=> Φ (k s))
      ⊢ wpi_mask GF Hd (act' (S := S) f k) Φ M := by
  simp only [act']
  refine .trans ?_ (wpi_bind (H := Hd) (act f) (fun s => ITree.ret (k s)) Φ M)
  /- Instantiate `wpi_act` at the intermediate postcondition that `wpi_bind`
  produced; giving it explicitly leaves no metavariable to solve. -/
  refine .trans ?_
    (wpi_act (SI := SI) f (fun s => wpi_mask GF Hd (ITree.ret (k s)) Φ M) M)
  /- All that is left is to weaken `Φ (k s)` to a trivial weakest precondition,
  under the state-passing that `wpi_act`'s premise wraps around it. -/
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

/-! ## The heap's ghost state

A `GhostMapG` at value type `Cell V = AccessState × V`, so the points-to
assertion records the access state next to the value — this is λRust's
`heap_pointsto_st`, and it is what makes the access-state guards of
`AeneasIris.Heap` provable rather than merely stated.

`Iris.genHeapGS` would have been the obvious thing to reuse, but it pins values
to `Type 0`: its meta-data table is stored in the *same* container `H` at value
type `GName`, and `GName : Type 0` forces `H : Type 0 → _`, hence
`V : Type 0`. Since the meta tokens are not needed here, going straight to
`GhostMapG` — which is universe-polymorphic — costs four short definitions and
keeps the heap usable at any universe. -/

section HeapGhost

variable {H : Type u → Type u} [Std.LawfulFiniteMap H Loc]
variable {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]

/-- The heap's ghost name, plus the resource it lives in. -/
class HeapGS (GF : BundledGFunctors) where
  ghost : GhostMapG GF Loc (Cell Val.{u}) HMap
  name : GName

attribute [reducible, instance] HeapGS.ghost

variable [G : HeapGS.{u} GF]

/-- The state interpretation: the ghost heap mirrors the physical heap exactly,
access states included. -/
def heapInterp : StateInterp RustHeap.{u} GF :=
  fun σ => ghost_map_auth G.name (DFrac.own 1) σ

/-- `l ↦[st]{dq} v`: the cell at `l` holds `v` and is in access state `st`. -/
def pointsToC (l : Loc) (dq : DFrac) (st : AccessState) (v : Val.{u}) : IProp GF :=
  ghost_map_elem (H := HMap) G.name dq l (st, v)

notation:50 l:51 " ↦[" st "]{" dq "} " v:51 => pointsToC l dq st v
notation:50 l:51 " ↦[" st "] " v:51 => pointsToC l (DFrac.own 1) st v

variable {E : Effect.{u+1}} [StateE RustHeap.{u} -< E]
variable {Hd : Handler E GF} [inH (stateH heapInterp.{u}) Hd]

/-- Reading off a cell known to be present. -/
private theorem valAt_of_get {σ : RustHeap.{u}} {l : Loc} {st : AccessState} {v : Val.{u}}
    (h : Std.get? σ l = some (st, v)) : valAt l σ = v := by
  simp only [valAt, h]

/-! ### Two shapes

Every heap operation either leaves the cell alone or replaces it. Proving those
two shapes once leaves each individual rule a four-line instance, and makes the
correspondence with λRust's `base_step` rules visible in the statements. -/

/-- Read-only: the guard accepts the state and returns it unchanged. Needs only
a fraction of the cell. -/
private theorem wpi_cell_ro {R : Type _} (l : Loc) (st : AccessState) (v : Val.{u}) (dq : DFrac)
    (f : RustHeap.{u} → Option (RustHeap.{u})) (k : RustHeap.{u} → R) (r : R)
    (Φ : Post GF R) (M : CoPset)
    (hf : ∀ σ : RustHeap.{u}, Std.get? σ l = some (st, v) → f σ = some σ)
    (hk : ∀ σ : RustHeap.{u}, Std.get? σ l = some (st, v) → k σ = r) :
    iprop(l ↦[st]{dq} v ∗ (l ↦[st]{dq} v -∗ |={M}=> Φ r))
      ⊢ wpi_mask GF Hd (act' (S := RustHeap.{u}) f k) Φ M := by
  refine .trans ?_ (wpi_act' (SI := heapInterp) f k Φ M)
  iintro ⟨Hl, HΦ⟩
  /- Close the mask down to `∅` for the duration of the event, keeping the wand
  that reopens it — the postcondition is stated at `M`. -/
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

/-- Read-modify-write: the guard accepts the state and replaces the cell.
Needs the full fraction, which is exactly what rules out a concurrent reader. -/
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

/-! ### Atomic accesses -/

/-- `wpi_load_at` (λRust `ReadScS`). An atomic read leaves the cell alone, so a
*fraction* of it suffices — and it tolerates non-atomic readers in flight,
since read/read never races. -/
theorem wpi_load_at (l : Loc) (n : Nat) (v : Val.{u}) (dq : DFrac) (Φ : Post GF Val.{u}) (M : CoPset) :
    iprop(l ↦[AccessState.reading n]{dq} v ∗
      (l ↦[AccessState.reading n]{dq} v -∗ |={M}=> Φ v))
      ⊢ wpi_mask GF Hd (load_at l) Φ M :=
  wpi_cell_ro l _ v dq _ (valAt l) v Φ M
    (fun _ h => by simp only [h]) (fun _ h => valAt_of_get h)

/-- `wpi_load_atT`. As `wpi_load_at`, with the projection folded in: the
points-to fixes the cell's type, so `Val.unpack_pack` applies and the read-off is
the identity. -/
theorem wpi_load_atT (T : Type u) [Inhabited T] (l : Loc) (n : Nat) (v : T) (dq : DFrac)
    (Φ : Post GF T) (M : CoPset) :
    iprop(l ↦[AccessState.reading n]{dq} Val.pack v ∗
      (l ↦[AccessState.reading n]{dq} Val.pack v -∗ |={M}=> Φ v))
      ⊢ wpi_mask GF Hd (load_atT T l) Φ M :=
  wpi_cell_ro l _ (Val.pack v) dq _ (fun σ => Val.unpack T (valAt l σ)) v Φ M
    (fun _ h => by simp only [h]) (fun _ h => by simp only [valAt_of_get h, Val.unpack_pack])

/-- `wpi_store_at` (λRust `WriteScS`). An atomic write demands an idle cell:
any non-atomic reader in flight would be a race. -/
theorem wpi_store_at (l : Loc) (v w : Val.{u}) (Φ : Post GF Unit) (M : CoPset) :
    iprop(l ↦[AccessState.reading 0] v ∗
      (l ↦[AccessState.reading 0] w -∗ |={M}=> Φ ()))
      ⊢ wpi_mask GF Hd (store_at l w) Φ M :=
  wpi_cell_upd l _ _ v w _ (fun _ => ()) () Φ M
    (fun _ h => by simp only [h]) (fun _ _ => rfl)

/-! ### Non-atomic accesses -/

/-- `wpi_readAcquire` (λRust `ReadNa1S`). -/
theorem wpi_readAcquire (l : Loc) (n : Nat) (v : Val.{u}) (Φ : Post GF Val.{u}) (M : CoPset) :
    iprop(l ↦[AccessState.reading n] v ∗
      (l ↦[AccessState.reading (n + 1)] v -∗ |={M}=> Φ v))
      ⊢ wpi_mask GF Hd (readAcquire l) Φ M :=
  wpi_cell_upd l _ _ v v _ (valAt l) v Φ M
    (fun _ h => by simp only [h]) (fun _ h => valAt_of_get h)

/-- `wpi_readRelease` (λRust `ReadNa2S`). -/
theorem wpi_readRelease (l : Loc) (n : Nat) (v : Val.{u}) (Φ : Post GF Unit) (M : CoPset) :
    iprop(l ↦[AccessState.reading (n + 1)] v ∗
      (l ↦[AccessState.reading n] v -∗ |={M}=> Φ ()))
      ⊢ wpi_mask GF Hd (readRelease l) Φ M :=
  wpi_cell_upd l _ _ v v _ (fun _ => ()) () Φ M
    (fun _ h => by simp only [h]) (fun _ _ => rfl)

/-- `wpi_writeAcquire` (λRust `WriteNa1S`). -/
theorem wpi_writeAcquire (l : Loc) (v : Val.{u}) (Φ : Post GF Unit) (M : CoPset) :
    iprop(l ↦[AccessState.reading 0] v ∗
      (l ↦[AccessState.writing] v -∗ |={M}=> Φ ()))
      ⊢ wpi_mask GF Hd (writeAcquire l) Φ M :=
  wpi_cell_upd l _ _ v v _ (fun _ => ()) () Φ M
    (fun _ h => by simp only [h]) (fun _ _ => rfl)

/-- `wpi_writeRelease` (λRust `WriteNa2S`). -/
theorem wpi_writeRelease (l : Loc) (v w : Val.{u}) (Φ : Post GF Unit) (M : CoPset) :
    iprop(l ↦[AccessState.writing] v ∗
      (l ↦[AccessState.reading 0] w -∗ |={M}=> Φ ()))
      ⊢ wpi_mask GF Hd (writeRelease l w) Φ M :=
  wpi_cell_upd l _ _ v w _ (fun _ => ()) () Φ M
    (fun _ h => by simp only [h]) (fun _ _ => rfl)

section NonAtomic

/-! The only two rules that need the concurrency effect. A non-atomic access is
two events with a `yield` between them, so the handler must be able to answer
`ConcE`; every other rule in this file is a single event. Scoping the
requirement here is what keeps it off the rest. -/

variable [ConcE -< E] [inH (ConcH GF) Hd]

/-- `wpi_load_na`.

Acquire, **yield**, release. The cell is back in its original state afterwards,
so the pre- and postconditions coincide — λRust's observation that `sc` and `na`
share a specification.

The mask is `⊤`, not arbitrary: the yield in the middle is a genuine scheduling
point, so no invariant may be held open across a non-atomic read. That is
exactly λRust's situation, where the two `base_step`s of `Read Na1Ord` are
separated by a scheduling point. -/
theorem wpi_load_na (l : Loc) (n : Nat) (v : Val.{u}) (Φ : Post GF Val.{u}) :
    iprop(l ↦[AccessState.reading n] v ∗
      (l ↦[AccessState.reading n] v -∗ |={⊤}=> Φ v))
      ⊢ wpi_mask GF Hd (load_na l) Φ ⊤ := by
  simp only [load_na]
  refine .trans ?_ (wpi_bind (H := Hd) (readAcquire l) _ Φ ⊤)
  refine .trans ?_ (wpi_readAcquire (Hd := Hd) l n v
    (fun v' => wpi_mask GF Hd
      (ITree.bind (yield) (fun _ =>
        ITree.bind (readRelease l) (fun _ => ITree.ret v'))) Φ ⊤) ⊤)
  iintro ⟨Hl, HΦ⟩
  iframe Hl
  iintro Hl
  imodintro
  /- The scheduling point: the yield forces the full mask, which is what makes
  this a genuinely non-atomic read. -/
  iapply (wpi_bind (H := Hd) (yield) _ Φ ⊤)
  iapply (wpi_yield GF (H := Hd)
    (fun _ => wpi_mask GF Hd
      (ITree.bind (readRelease l) (fun _ => ITree.ret v)) Φ ⊤))
  iapply (wpi_bind (H := Hd) (readRelease l) _ Φ ⊤)
  iapply (wpi_readRelease (Hd := Hd) l n v _ ⊤)
  isplitl [Hl]
  · iexact Hl
  iintro Hl
  imodintro
  iapply (wpi_ret' (H := Hd) v Φ ⊤).mp
  iapply HΦ $$ Hl

/-- `wpi_store_na`. Acquire the write lock, **yield**, then release storing `w`.

Like `wpi_load_na` the mask is `⊤`: the cell sits in the `writing` state across
the scheduling point, which is precisely the window λRust's `WriteNa1S`/
`WriteNa2S` pair leaves open, and no invariant may span it. -/
theorem wpi_store_na (l : Loc) (v w : Val.{u}) (Φ : Post GF Unit) :
    iprop(l ↦[AccessState.reading 0] v ∗
      (l ↦[AccessState.reading 0] w -∗ |={⊤}=> Φ ()))
      ⊢ wpi_mask GF Hd (store_na l w) Φ ⊤ := by
  simp only [store_na]
  refine .trans ?_ (wpi_bind (H := Hd) (writeAcquire l) _ Φ ⊤)
  refine .trans ?_ (wpi_writeAcquire (Hd := Hd) l v
    (fun _ => wpi_mask GF Hd
      (ITree.bind (yield) (fun _ => writeRelease l w)) Φ ⊤) ⊤)
  iintro ⟨Hl, HΦ⟩
  iframe Hl
  iintro Hl
  imodintro
  iapply (wpi_bind (H := Hd) (yield) _ Φ ⊤)
  iapply (wpi_yield GF (H := Hd)
    (fun _ => wpi_mask GF Hd (writeRelease l w) Φ ⊤))
  iapply (wpi_writeRelease (Hd := Hd) l v w Φ ⊤)
  isplitl [Hl]
  · iexact Hl
  iexact HΦ

end NonAtomic

/-! ### Read-modify-write -/

/-- `wpi_cas`, succeeding arm (λRust `CasSucS`). A CAS that writes demands an
idle cell. -/
theorem wpi_cas_suc [DecidableEq Val.{u}] (l : Loc) (old new : Val.{u}) (Φ : Post GF Bool) (M : CoPset) :
    iprop(l ↦[AccessState.reading 0] old ∗
      (l ↦[AccessState.reading 0] new -∗ |={M}=> Φ true))
      ⊢ wpi_mask GF Hd (cas l old new) Φ M := by
  simp only [cas]
  refine wpi_cell_upd l _ _ old new _ _ true Φ M
    (fun _ h => by simp only [h]; simp) (fun _ h => by simp only [h]; simp)

/-- `wpi_cas_fail` (λRust `CasFailS`). A CAS that is going to fail only reads,
so — like an atomic load — a fraction suffices and readers may be in flight. -/
theorem wpi_cas_fail [DecidableEq Val.{u}] (l : Loc) (n : Nat) (v old new : Val.{u}) (dq : DFrac)
    (hne : v ≠ old) (Φ : Post GF Bool) (M : CoPset) :
    iprop(l ↦[AccessState.reading n]{dq} v ∗
      (l ↦[AccessState.reading n]{dq} v -∗ |={M}=> Φ false))
      ⊢ wpi_mask GF Hd (cas l old new) Φ M := by
  simp only [cas]
  refine wpi_cell_ro l _ v dq _ _ false Φ M
    (fun _ h => by cases n <;> simp only [h] <;> simp [hne])
    (fun _ h => by simp only [h]; simp [hne])

/-- `wpi_modify`. An atomic read-modify-write returns the *old* value; it is one event, which is
why it needs no second read. -/
theorem wpi_modify (f : Val.{u} → Val.{u}) (l : Loc) (v : Val.{u})
    (Φ : Post GF Val.{u}) (M : CoPset) :
    iprop(l ↦[AccessState.reading 0] v ∗
      (l ↦[AccessState.reading 0] (f v) -∗ |={M}=> Φ v))
      ⊢ wpi_mask GF Hd (modify f l) Φ M := by
  simp only [modify]
  refine wpi_cell_upd l _ _ v (f v) _ (valAt l) v Φ M
    (fun _ h => by simp only [h]) (fun _ h => valAt_of_get h)

/-- `wpi_modifyT`. An atomic read-modify-write at a type returns the old value
and installs `f` of it. -/
theorem wpi_modifyT (T : Type u) [Inhabited T] (f : T → T) (l : Loc) (v : T)
    (Φ : Post GF T) (M : CoPset) :
    iprop(l ↦[AccessState.reading 0] Val.pack v ∗
      (l ↦[AccessState.reading 0] Val.pack (f v) -∗ |={M}=> Φ v))
      ⊢ wpi_mask GF Hd (modifyT T f l) Φ M :=
  wpi_cell_upd l _ _ (Val.pack v) (Val.pack (f v)) _
    (fun σ => Val.unpack T (valAt l σ)) v Φ M
    (fun _ h => by simp only [h, Val.unpack_pack])
    (fun _ h => by simp only [valAt_of_get h, Val.unpack_pack])

/-! ### Allocation and deallocation -/

/-- `wpi_alloc`. One event, so no other thread can observe a half-built cell.
The location is not chosen by the caller — it comes back in the postcondition. -/
theorem wpi_alloc (v : Val.{u}) (Φ : Post GF Loc) (M : CoPset) :
    iprop(∀ l, l ↦[AccessState.reading 0] v -∗ |={M}=> Φ l)
      ⊢ wpi_mask GF Hd (alloc v) Φ M := by
  simp only [alloc]
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

/-- `wpi_free`. Deallocation consumes the cell, and demands it be idle. -/
theorem wpi_free (l : Loc) (v : Val.{u}) (Φ : Post GF Unit) (M : CoPset) :
    iprop(l ↦[AccessState.reading 0] v ∗ |={M}=> Φ ())
      ⊢ wpi_mask GF Hd (free l) Φ M := by
  simp only [free]
  refine .trans ?_ (wpi_act' (SI := heapInterp) _ (fun _ => ()) Φ M)
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
