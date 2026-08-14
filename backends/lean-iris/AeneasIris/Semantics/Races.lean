import AeneasIris.Semantics.Soundness

/-!
# Data-race freedom, stated explicitly

Races are genuinely modelled — they are not assumed away — but until now they
were only *implicit*: a racing access is one of the many things that makes
`Config.Faulty` hold, and `Safe` rules them out along with out-of-bounds
accesses and type confusion. This file separates the strand out, so that
"the program has no data races" is a theorem one can point at, with a definition
of *race* that does not mention the word "stuck".

## How races are modelled

`RustHeap` maps a location to `AccessState × Val`, and `AccessState` is λRust's
read/write state machine (`Aeneas.Std.AccessState`, from `lambda-rust/lang/lang.v`):

* `reading n` — `n` readers are inside a non-atomic read;
* `writing` — a writer is inside a non-atomic write.

A non-atomic access is *not* one event. `Heap.load_na l = readAcquire l; yield;
readRelease l` and `Heap.store_na l v = writeAcquire l; yield; writeRelease l v`
— the `yield` in the middle is exactly the window in which another thread may
observe the access in progress. The state transitions enforce the discipline:

| operation | requires | leaves |
|---|---|---|
| `readAcquire` | `reading n` | `reading (n+1)` |
| `readRelease` | `reading (n+1)` | `reading n` |
| `writeAcquire` | `reading 0` | `writing` |
| `writeRelease` | `writing` | `reading 0` |
| `load_at` | `reading _` | access state unchanged |
| `store_at`, `modify` | `reading 0` | `reading 0`, new value |
| `cas` (succeeds) | `reading 0` | `reading 0`, new value |
| `cas` (fails, `v ≠ old`) | `reading _` | unchanged |

The `cas` rows are worth spelling out: a **failed** compare-and-swap is only a
read, so `Heap.cas_body` accepts `reading (n+1)` in that case — it is faithful
to λRust's `CasFailS`/`CasStuckS` split, and a table that lumped all of `cas`
under `reading 0` would misdescribe it.

So a conflicting pair leaves the heap in a state where the second access has no
transition: two concurrent `store_na`s collide because the second `writeAcquire`
finds `writing`; a `load_na` racing a `store_na` collides for the same reason;
two concurrent `load_na`s do *not* collide, because `reading n → reading (n+1)`
is always available. Atomics never race with each other: each is a single event
with no `yield`, so no other thread can run in between.

A race is therefore a configuration in which the scheduled thread's heap
operation is undefined. That is `Config.Faulty` — which is why race freedom
falls out of `Safe`. What this file adds is a definition that says *why* the
operation is undefined, so that the theorem cannot be confused with "the machine
happened to halt".

## The definition, and why it is not circular

`StateE`'s single primitive is `modify : RustHeap → Option RustHeap`, and the
event does not record which location it touches — so the machine cannot see a
"conflicting pair" directly. Instead we characterise a race by *what would have
to change to make the operation succeed*: `RacesOn σ f` says `f` is undefined at
`σ`, yet there is a heap with **the same contents** on which it succeeds. Since
the two heaps differ only in their `AccessState`s, the failure cannot be
out-of-bounds (the domains agree) and cannot be type confusion (the values
agree): the access-state discipline is the only thing left to blame.

`racesOn_writeAcquire` and `racesOn_readAcquire` below show the definition is not
vacuous, by exhibiting the two conflicting pairs.
-/

namespace AeneasIris.Semantics

open Iris
open Aeneas.Data.Coinductive
open Aeneas.Std (Result RustEffect RustHeap Loc AccessState Val Cell)
open Std.PartialMap

unseal Aeneas.Std.Result

/-! ## Racing -/

/-- Two heaps store the same value at every location, differing at most in their
`AccessState`s.

One condition suffices: if one heap has a cell where the other has none, the
`Option`s differ already, so the domains agree too. -/
def SameContents (σ σ' : RustHeap.{0}) : Prop :=
  ∀ l : Loc, (get? σ l).map Prod.snd = (get? σ' l).map Prod.snd

theorem SameContents.refl (σ : RustHeap.{0}) : SameContents σ σ := fun _ => rfl

/-- **A data race.** The heap operation `f` is undefined at `σ`, but succeeds on
a heap with the same contents — so the only thing standing in its way is another
thread's access state.

This deliberately excludes the other two ways a heap operation can be undefined:
an out-of-bounds access fails on every heap with the same domain, and a
type-mismatched access fails on every heap with the same values. -/
def RacesOn (σ : RustHeap.{0}) (f : RustHeap.{0} → Option RustHeap.{0}) : Prop :=
  f σ = none ∧ ∃ σ', SameContents σ σ' ∧ (f σ').isSome

/-- The scheduled thread is about to race. -/
def Config.Racing {α : Type} (c : Config α) : Prop :=
  ∃ (f : RustHeap.{0} → Option RustHeap.{0}) (k : RustEffect.O (modifyEv f) → Result α),
    c.focus = some (Result.vis (modifyEv f) k) ∧ RacesOn c.heap f

/-- **No execution of `t` ever reaches a data race.** -/
def DataRaceFree {α : Type} (t : Result α) : Prop :=
  ∀ c, Reaches (init t) c → ¬ c.Racing

/-! ## Race freedom -/

/-- A racing configuration is a faulty one: `RacesOn` implies the operation is
undefined here, which is `StuckOn`. -/
theorem Config.Racing.faulty {α : Type} {c : Config α} (h : c.Racing) : c.Faulty := by
  obtain ⟨f, k, hfoc, hnone, -⟩ := h
  exact ⟨_, hfoc, .inr ⟨f, k, rfl, hnone⟩⟩

/-- **Safety implies race freedom.** -/
theorem dataRaceFree_of_safe {α : Type} {t : Result α} (h : Safe t) : DataRaceFree t :=
  fun c hr hrace => h c hr hrace.faulty

/-- **The headline: one `wpi` triple rules out data races.**

Note this is race freedom for *every* schedule, since `Step.yield` may hand
control to any live thread and `Reaches` quantifies over all such chains. -/
theorem dataRaceFree_of_provable {α : Type} {t : Result α} {φ : α → Prop}
    (h : ProvableSpecOf .part t φ) : DataRaceFree t :=
  dataRaceFree_of_safe (safe_of_provable h)

/-! ## The definition has content

Two lemmas exhibiting the two conflicting pairs. Without these, `DataRaceFree`
could be vacuously true because `RacesOn` was empty.

The transformers below are not paraphrases of the real operations: `writeAcquireF_eq`
and `readAcquireF_eq` prove they are *literally* the functions inside
`Heap.writeAcquire_body` and `Heap.readAcquire_body`. Without those two, the
witnesses would be about hand-written copies, and a divergence between copy and
original would go unnoticed — exactly the hole a non-vacuity argument is supposed
to close. -/

/-- `writeAcquire`'s state transformer; see `writeAcquireF_eq`. -/
def writeAcquireF (l : Loc) : RustHeap.{0} → Option RustHeap.{0} := fun σ =>
  match get? σ l with
  | some (AccessState.reading 0, v) => some (insert σ l (AccessState.writing, v))
  | _ => none

/-- `readAcquire`'s state transformer; see `readAcquireF_eq`. -/
def readAcquireF (l : Loc) : RustHeap.{0} → Option RustHeap.{0} := fun σ =>
  match get? σ l with
  | some (AccessState.reading n, v) => some (insert σ l (AccessState.reading (n + 1), v))
  | _ => none

/-- `writeAcquireF` really is the transformer `Heap.writeAcquire_body` triggers. -/
theorem writeAcquireF_eq (l : Loc) :
    (AeneasIris.Heap.writeAcquire_body (E := Aeneas.Std.RustEffect) l :
        ITree Aeneas.Std.RustEffect PUnit.{1})
      = AeneasIris.Heap.act' (S := RustHeap.{0}) (writeAcquireF l) (fun _ => PUnit.unit) :=
  rfl

/-- `readAcquireF` really is the transformer `Heap.readAcquire_body` triggers. -/
theorem readAcquireF_eq (l : Loc) :
    (AeneasIris.Heap.readAcquire_body (E := Aeneas.Std.RustEffect) l :
        ITree Aeneas.Std.RustEffect Val.{0})
      = ITree.bind
          (AeneasIris.Heap.act' (S := RustHeap.{0}) (readAcquireF l)
            (AeneasIris.Heap.valAt l))
          (fun o => match o with
                    | some v => ITree.ret v
                    | none => AeneasIris.Heap.panic) :=
  rfl

/-- **Write ∥ read is a race.** A thread starting a non-atomic write to a cell
that another thread is reading has no transition, and clearing the reader would
give it one. -/
theorem racesOn_writeAcquire (σ : RustHeap.{0}) (l : Loc) (n : Nat) (v : Val.{0})
    (h : get? σ l = some (AccessState.reading (n + 1), v)) :
    RacesOn σ (writeAcquireF l) := by
  refine ⟨by simp only [writeAcquireF, h], insert σ l (AccessState.reading 0, v), ?_, ?_⟩
  · intro l'
    by_cases hl : l = l'
    · subst hl; simp only [h, Std.get?_insert_eq (rfl : l = l)]; rfl
    · simp only [Std.get?_insert_ne hl]
  · simp only [writeAcquireF, Std.get?_insert_eq (rfl : l = l)]
    rfl

/-- **Read ∥ write is a race.** A thread starting a non-atomic read of a cell
that another thread is writing has no transition. -/
theorem racesOn_readAcquire (σ : RustHeap.{0}) (l : Loc) (v : Val.{0})
    (h : get? σ l = some (AccessState.writing, v)) :
    RacesOn σ (readAcquireF l) := by
  refine ⟨by simp only [readAcquireF, h], insert σ l (AccessState.reading 0, v), ?_, ?_⟩
  · intro l'
    by_cases hl : l = l'
    · subst hl; simp only [h, Std.get?_insert_eq (rfl : l = l)]; rfl
    · simp only [Std.get?_insert_ne hl]
  · simp only [readAcquireF, Std.get?_insert_eq (rfl : l = l)]
    rfl

/-- **Read ∥ read is not a race**, which is what makes the previous two lemmas
say something: `readAcquire` always has a transition on a cell that is only
being read, however many readers there are. -/
theorem readAcquire_not_stuck (σ : RustHeap.{0}) (l : Loc) (n : Nat) (v : Val.{0})
    (h : get? σ l = some (AccessState.reading n, v)) :
    (readAcquireF l σ).isSome := by
  simp only [readAcquireF, h]
  rfl

end AeneasIris.Semantics
