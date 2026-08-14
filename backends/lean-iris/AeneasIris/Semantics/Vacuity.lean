import AeneasIris.Semantics.Races
import AeneasIris.Semantics.Soundness
import AeneasIris.Tactics.Core

/-!
# The properties are not trivially true

Every theorem in this development has the shape "… therefore **nothing bad
happens**": `¬ c.Faulty`, `¬ c.Racing`, `¬ Diverging`. Such a statement is worth
exactly as much as the badness it excludes. If `Config.Faulty` happened to be
unsatisfiable — a mis-stated `Panics`, an injection that no `Result` can match,
a `StuckOn` whose `f σ = none` can never hold — then `Safe` would be true of
every program, `adequacy_part` would be a tautology, and nothing in
`Example.lean` would reveal it, because `Example.lean` only ever proves the
*good* side.

This file proves the bad side: concrete programs that **are** unsafe, and a
configuration that **is** racing. It is the mirror of `Example.lean` and should
be read with it.

None of it is used by any other module. It exists to be checked.

## What is witnessed here

| witnessed | theorem |
|---|---|
| a program that panics | `panicProg_faulty`, `panicProg_unsafe` |
| a program that performs an undefined heap operation | `loadProg_faulty`, `loadProg_unsafe` |
| hence `Safe` is a real restriction | `exists_unsafe` |
| hence `Panics` and `StuckOn` are both inhabited | the two above, separately |
| a configuration that is racing | `racingConfig_racing` |
| a **reachable** data race | `race_reachable`, `cRace_racing`, `racer_not_race_free` |
| hence the logic *forbids* racy programs | `racer_unprovable` |

The two unsafe programs fault at `init` itself, so `Reaches.refl` suffices and
no trace machinery is needed. That is deliberate: a witness whose proof is one
constructor cannot itself be hiding a mistake. The race witness does need a
trace — five steps, exercising `heap`, `fork` and `yield` — because racing is
inherently a multi-thread phenomenon.

`racer_unprovable` is the strongest statement here: for the racy program, **no
`wpi` triple exists at all**, for any postcondition. It is the contrapositive of
`safe_of_provable`, and it is what makes race freedom a *consequence* of the
logic rather than a coincidence.

## On the hand-built configuration

`racingConfig` is built by hand rather than reached from an `init`. On its own
that would be a weak witness — `DataRaceFree` quantifies over *reachable*
configurations, so inhabitation of `Config.Racing` proves nothing about it. The
`racer` section at the end of this file closes that properly, with an execution
trace; `racingConfig` is kept because it isolates the racing predicate from the
trace machinery, and the two together say more than either alone.

## A note on how the threads are written

`loadProg` and `racingConfig`'s thread are written as `Result.vis (modifyEv …) …`
nodes directly, not as `Heap.load_body` / `Heap.readAcquire_body`. That is not
laziness: `Heap.act'` is a `bind` of a `vis`, and `ITree.bind` is a
`partial_fixpoint`, so `bind`-on-`vis` is a *theorem* and never a definitional
equality — a hand-written node keeps every proof here a one-constructor term.

The link to the real operations is not lost, it is relocated: `loadF_eq` (this
file) and `readAcquireF_eq` (`Races.lean`) prove **by `rfl`** that the state
transformers used here are literally the ones the real operations trigger. This
is the same discipline `Races.lean` already uses, and it is the part that
matters — a divergence between a hand-written copy and the original is exactly
the hole a non-vacuity argument is supposed to close.
-/

namespace AeneasIris.Semantics

open Iris
open Aeneas.Data.Coinductive
open Aeneas.Std (Result RustEffect RustHeap Error Loc AccessState Cell Val HMap ConcE)
open Std.PartialMap
open scoped Aeneas.Std
open scoped Aeneas
open scoped AeneasIris

unseal Aeneas.Std.Result

/-! ## A program that panics -/

/-- The shortest panicking program: Aeneas emits exactly this for a failing
`assert!`, an integer overflow, or an out-of-bounds index. -/
def panicProg : Result Nat := Result.fail Error.panic

/-- `panicProg` sits on a `fail` node — `Panics` is inhabited. -/
theorem panicProg_panics : Panics panicProg :=
  ⟨Error.panic, PEmpty.elim, rfl⟩

/-- The initial configuration of `panicProg` is already faulty. -/
theorem panicProg_faulty : (init panicProg).Faulty :=
  ⟨panicProg, rfl, Or.inl panicProg_panics⟩

/-- **`Safe` is not trivially true.** -/
theorem panicProg_unsafe : ¬ Safe panicProg := fun h =>
  h (init panicProg) (.refl _) panicProg_faulty

/-! ## A program that performs an undefined heap operation

Not a panic: a *load from a location that was never allocated*. On the machine
this is a `modify` whose transformer returns `none`, which is what `StuckOn`
means. Rust's type system rules it out at the source level; the point is that
the machine does not, so `Safe` has to. -/

/-- The transformer inside `Heap.load_body`, spelled out. Compare `Races.lean`'s
`readAcquireF`: the same technique, and `loadF_eq` below is again `rfl`, so this
is the real operation and not a lookalike. -/
noncomputable def loadF (T : Type) (l : Loc) : RustHeap.{0} → Option RustHeap.{0} :=
  fun σ => match Std.get? σ l with
    | some (AccessState.reading _, v) => if v.1 = T then some σ else none
    | _ => none

theorem loadF_eq (T : Type) [Nonempty T] (l : Loc) :
    Heap.load_body (E := RustEffect) T l
      = Heap.act' (loadF T l) (fun σ => Val.unpack T (Heap.valAt l σ)) := rfl

/-- The two monads' `bind`s agree; kept because it is `rfl` and documents that
`Result`'s bind is `ITree`'s. -/
theorem itree_bind_eq_std.{ua, ub} {α : Type ua} {β : Type ub}
    (t : Result α) (f : α → Result β) :
    ITree.bind t f = Aeneas.Std.bind t f := rfl

/-- Some location. Which one is irrelevant: the initial heap is empty. -/
def someLoc : Loc := Std.fresh (M := HMap.{1}) (K := Loc) (V := Cell.{1} Val.{0})
  (m := (∅ : RustHeap.{0})) trivial

/-- A thread about to load from a never-allocated location.

Written as the `modify` node directly rather than as `Heap.load_body`, for the
same reason `Races.lean` writes `readAcquireF` by hand: `Heap.act'` is a `bind`
of a `vis`, and `ITree.bind` is a `partial_fixpoint`, so `bind`-on-`vis` is a
theorem and never a definitional equality. Writing the node by hand keeps every
proof below a one-constructor term.

Nothing is lost, because `loadF_eq` above proves **by `rfl`** that `loadF Nat l`
is exactly the transformer inside `Heap.load_body Nat l`. The witness therefore
concerns the real load, not a lookalike — this is the same discipline as
`Races.lean`'s `readAcquireF_eq`/`writeAcquireF_eq`. -/
noncomputable def loadProg : Result Nat :=
  Result.vis (modifyEv (loadF Nat someLoc)) (fun _ => Result.ok 0)

/-- The empty heap has nothing at `someLoc`, so the transformer is undefined. -/
theorem loadF_empty : loadF Nat someLoc (∅ : RustHeap.{0}) = none := rfl

/-- `loadProg` is stuck on the empty heap — `StuckOn` is inhabited. -/
theorem loadProg_stuck : StuckOn (∅ : RustHeap.{0}) loadProg :=
  ⟨loadF Nat someLoc, _, rfl, loadF_empty⟩

theorem loadProg_faulty : (init loadProg).Faulty :=
  ⟨loadProg, rfl, Or.inr loadProg_stuck⟩

/-- **`Safe` excludes undefined heap operations too**, and not vacuously. -/
theorem loadProg_unsafe : ¬ Safe loadProg := fun h =>
  h (init loadProg) (.refl _) loadProg_faulty

/-- **The headline.** There exist unsafe programs, so `safe_of_provable` says
something. Together with `Example.lean`'s `prog_spec` — a program that *does*
satisfy the hypothesis — both sides of the implication are inhabited. -/
theorem exists_unsafe : ∃ t : Result Nat, ¬ Safe t := ⟨panicProg, panicProg_unsafe⟩

/-! ## A racing configuration

`Races.lean` proves `racesOn_readAcquire`: on a heap where `l` is being written,
the *real* `Heap.readAcquire_body` transformer is undefined, while on a heap with
the same contents where `l` is free it is defined. Lifting that to a whole
configuration shows `Config.Racing` is inhabited. -/

/-- A heap in which `l` is checked out for writing, holding some value. -/
noncomputable def writingHeap (l : Loc) (v : Val.{0}) : RustHeap.{0} :=
  Std.insert (∅ : RustHeap.{0}) l (AccessState.writing, v)

/-- A configuration whose scheduled thread is about to take a read lock on a
location that another thread holds for writing.

The thread is written as the `modify` node itself rather than as a `bind` of
`Heap.readAcquire_body`, because `bind`-on-`vis` is a theorem and not a
definitional equality (`ITree.bind` is a `partial_fixpoint`). Nothing is lost:
`Races.readAcquireF_eq` proves by `rfl` that `readAcquireF l` is exactly the
transformer `Heap.readAcquire_body l` triggers, so this thread is about to
perform the real operation. -/
noncomputable def racingConfig (l : Loc) (v : Val.{0}) : Config Nat :=
  { threads := [.alive (Result.vis (modifyEv (readAcquireF l)) (fun _ => Result.ok 0))],
    current := 0,
    heap := writingHeap l v }

/-- The heap really does have `l` checked out for writing. -/
theorem writingHeap_get (l : Loc) (v : Val.{0}) :
    get? (writingHeap l v) l = some (AccessState.writing, v) := by
  simp only [writingHeap, Std.get?_insert_eq (rfl : l = l)]

/-- **`Config.Racing` is inhabited.** -/
theorem racingConfig_racing (l : Loc) (v : Val.{0}) : (racingConfig l v).Racing :=
  ⟨readAcquireF l, _, rfl, racesOn_readAcquire _ l v (writingHeap_get l v)⟩

/-- Hence the race-freedom conclusion excludes something. -/
theorem exists_racing : ∃ c : Config Nat, c.Racing :=
  ⟨racingConfig someLoc (Val.pack (0 : Nat)), racingConfig_racing _ _⟩

/-- And a racing configuration is faulty, so `Safe` rules it out. -/
theorem racingConfig_faulty (l : Loc) (v : Val.{0}) : (racingConfig l v).Faulty :=
  (racingConfig_racing l v).faulty


/-! ## A *reachable* data race

The witnesses above show `Config.Racing` is inhabited, but `DataRaceFree`
quantifies over configurations **reachable from an `init`**, so inhabitation
alone leaves the possibility that no honest execution ever gets there. This
section closes that: a two-thread program that genuinely races, with the trace
written out.

The shape is the smallest one that races. The parent allocates, forks, and
yields to the child; the child takes a write lock and yields back; the parent
then attempts its own write lock on the same location. That last operation is
undefined — and it is undefined *because of the access state*, not because the
location is missing or ill-typed, which is exactly what `RacesOn` requires.

`racer_unprovable` is the payoff and the strongest single statement in this
file: **no `wpi` triple whatsoever can be proved for this program**, for any
postcondition. Soundness is not merely consistent with race freedom; it forbids
the racy program outright. -/

/-- Allocate location `0`, unlocked.

Unlike `readAcquireF`, `loadF` and the transformers in `RustBelt.lean`, this one
is **not** a copy of any operation in `Effects/Heap.lean`, so there is nothing to
tie it back to and it has no `_eq` lemma. It is this test program's own setup
step, written directly because `alloc` picks a fresh location and the trace below
needs to name the location it allocated. Anything that audits "every hand-written
transformer is pinned to a real operation by `rfl`" should skip it for that
reason, not conclude that one is missing. -/
def setupF : RustHeap.{0} → Option RustHeap.{0} :=
  fun σ => some (Std.insert σ 0 (AccessState.reading 0, Val.pack (0 : Nat)))

/-- The child: take a write lock on `0`, then yield back. -/
noncomputable def child : Result Nat :=
  Result.vis (modifyEv (writeAcquireF 0)) (fun _ =>
    Result.vis yieldEv (fun _ => Result.ok 1))

/-- The parent after forking: yield, then take a write lock on `0`. -/
noncomputable def parent : Result Nat :=
  Result.vis yieldEv (fun _ =>
    Result.vis (modifyEv (writeAcquireF 0)) (fun _ => Result.ok 0))

/-- Setup, fork, and the two branches. -/
noncomputable def racer : Result Nat :=
  Result.vis (modifyEv setupF) (fun _ =>
    Result.vis forkEv (fun tag => match tag with
      | ConcE.Tags.cur => parent
      | ConcE.Tags.new => child))

/-- After setup: `0` allocated and unlocked. -/
def h0 : RustHeap.{0} :=
  Std.insert (∅ : RustHeap.{0}) 0 (AccessState.reading 0, Val.pack (0 : Nat))

/-- After the child's write lock: `0` checked out for writing. -/
def h1 : RustHeap.{0} := Std.insert h0 0 (AccessState.writing, Val.pack (0 : Nat))

theorem setup_ok : setupF ∅ = some h0 := rfl

theorem wa_h0 : writeAcquireF 0 h0 = some h1 := by
  simp only [writeAcquireF, h0, Std.get?_insert_eq (rfl : (0 : Loc) = 0)]; rfl

/-- The parent's write lock has no transition at `h1`. -/
theorem wa_h1 : writeAcquireF 0 h1 = none := by
  simp only [writeAcquireF, h1, Std.get?_insert_eq (rfl : (0 : Loc) = 0)]

/-- The racing configuration: the parent scheduled and about to write, the child
holding the write lock. -/
noncomputable def cRace : Config Nat :=
  ⟨[Thread.alive (Result.vis (modifyEv (writeAcquireF 0)) (fun _ => Result.ok 0)),
    Thread.alive (Result.ok 1)], 0, h1⟩

/-- **Five machine steps to a data race**: `heap`, `fork`, `yield`, `heap`,
`yield`. Every rule but `tick` and `endthread` appears. -/
theorem race_reachable : Reaches (init racer) cRace := by
  refine .tail (Step.heap (c := init racer) rfl setup_ok) ?_
  refine .tail (Step.fork (c := ⟨[Thread.alive _], 0, h0⟩) rfl) ?_
  refine .tail (Step.yield (c := ⟨[Thread.alive parent, Thread.alive child], 0, h0⟩)
                  (j := 1) rfl ⟨child, rfl⟩) ?_
  refine .tail (Step.heap (c := ⟨[Thread.alive _, Thread.alive child], 1, h0⟩) rfl wa_h0) ?_
  refine .tail (Step.yield (c := ⟨[Thread.alive _, Thread.alive _], 1, h1⟩)
                  (j := 0) rfl ⟨_, rfl⟩) ?_
  exact .refl _

theorem g_h1_0 : get? h1 0 = some (AccessState.writing, Val.pack (0 : Nat)) :=
  Std.get?_insert_eq (rfl : (0 : Loc) = 0)

theorem g_h0_0 : get? h0 0 = some (AccessState.reading 0, Val.pack (0 : Nat)) :=
  Std.get?_insert_eq (rfl : (0 : Loc) = 0)

/-- **It really is a race**: the operation is undefined at `h1`, and `h0` has the
same contents but a clear access state, where it succeeds. -/
theorem cRace_racing : cRace.Racing := by
  refine ⟨writeAcquireF 0, (fun _ => Result.ok 0), rfl, wa_h1, h0, ?_, ?_⟩
  · intro l
    by_cases hl : (0 : Loc) = l
    · subst hl
      show (get? h1 0).map _ = (get? h0 0).map _
      rw [g_h1_0, g_h0_0]; rfl
    · show (get? (Std.insert h0 0 (AccessState.writing, Val.pack (0 : Nat))) l).map _
          = (get? h0 l).map _
      rw [Std.get?_insert_ne hl]
  · rw [wa_h0]; rfl

/-- **`DataRaceFree` is a real restriction.** -/
theorem racer_not_race_free : ¬ DataRaceFree racer :=
  fun h => h cRace race_reachable cRace_racing

theorem racer_unsafe : ¬ Safe racer :=
  fun h => h cRace race_reachable cRace_racing.faulty

/-- **The logic forbids the racy program.** Contrapositive of
`safe_of_provable`: no `wpi` triple exists for `racer`, whatever the
postcondition. -/
theorem racer_unprovable (φ : Nat → Prop) : ¬ ProvableSpecOf .part racer φ :=
  fun h => racer_unsafe (safe_of_provable h)

end AeneasIris.Semantics
