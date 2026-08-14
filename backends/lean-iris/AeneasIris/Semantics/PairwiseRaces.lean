import AeneasIris.Semantics.RustBelt
import AeneasIris.Semantics.Vacuity

/-!
# λRust's pairwise race notion, and exactly what is missing

`Races.lean` defines a race the way this machine can observe one: the scheduled
thread's operation is refused, and a heap with the same contents would have
allowed it. λRust instead defines it **pairwise over the thread pool** — two
threads each *about to* touch one location with incompatible access kinds — and
that statement is the one that lines up with the C11 / Rust-book notion of a data
race.

This file brings the pairwise notion over, proves λRust's compatibility table for
it, and then isolates — as a single named hypothesis — the one thing that stops
`Safe` from implying it here.

## The upgrade is genuinely an upgrade, in one respect

λRust needs a **second description of its own semantics** to say this:
`next_access_head` classifies a redex as `(ReadAcc | WriteAcc | FreeAcc, order)`,
and nothing in Coq forces it to agree with `head_step` — hence the warning
comment above it (quoted in `RustBelt.lean`).

`Conflict` below needs no such thing. Two pending operations conflict when
**performing one disables the other**, which is stated about the transformers the
machine actually runs. There is no second description, so there is nothing to
keep in sync, and the compatibility table is a *theorem* rather than a
definition.

## What is missing, and why it is not a proof gap

`Safe` constrains the **scheduled** thread. To turn "threads `i` and `j` are
poised on conflicting operations" into a contradiction one must *run* `i` and
then *schedule* `j` — and in this machine control moves only at `yield`. If the
thread holding the lock diverges, or returns (which freezes the machine — see
`All.lean`), neither `i` nor `j` ever runs, and no configuration is ever
`Faulty`.

λRust does not meet this obstacle because its scheduler is external: any thread
may step next, always. Ours is cooperative, and that is not an oversight — it is
the same decision that lets `wpi_open_invariant` drop the atomicity side
condition, because "atomic" here means "yield-free" (`Invariant.lean`). **A
preemption rule would break the big lock**: preempting a thread mid-computation
means parking it at mask `⊤`, which requires it to hand back `ownE ⊤`, which it
cannot do in the middle of a yield-free region.

So the honest position is:

* the **proof** has no gap — `adequacy_part` and `adequacy_total` are complete and
  axiom-clean;
* the **model** is cooperative where Rust is preemptive, and the pairwise
  statement is exactly what that costs;
* `SchedulableAfter` below names the missing premise. It is discharged for free
  by a preemptive machine and not by this one.

Everything here is stated for the manifested-conflict direction. `Races.lean`'s
`DataRaceFree` remains the unconditional result.
-/

namespace AeneasIris.Semantics

open Iris
open Aeneas.Data.Coinductive
open Aeneas.Std (Result RustEffect RustHeap Loc AccessState Val Cell ConcE)
open Std.PartialMap
open AeneasIris.Semantics.RustBelt

unseal Aeneas.Std.Result

/-! ## The pairwise notion -/

/-- Thread `i` of `c` is about to perform the heap operation `f`.

Unlike λRust's `next_access_head` this inspects no syntax and classifies
nothing: `f` is the transformer the machine will run. -/
def PendingOp {α : Type} (c : Config α) (i : Nat)
    (f : RustHeap.{0} → Option RustHeap.{0}) : Prop :=
  ∃ k, c.threads[i]? = some (.alive (Result.vis (modifyEv f) k))

/-- **Two pending operations conflict at `σ` when performing one disables the
other.**

This is λRust's `nonracing_accesses` without the detour through access kinds and
orderings. `(ReadAcc, _), (ReadAcc, _) => True` and
`(_, ScOrd), (_, ScOrd) => True` are recovered below as theorems, not stipulated
as a table. -/
def Conflict (σ : RustHeap.{0}) (f g : RustHeap.{0} → Option RustHeap.{0}) : Prop :=
  (∃ σ', f σ = some σ' ∧ g σ' = none) ∨ (∃ σ', g σ = some σ' ∧ f σ' = none)

theorem Conflict.symm {σ f g} (h : Conflict σ f g) : Conflict σ g f := Or.symm h

/-- **λRust's `nonracing_threadpool`, here.** Two *distinct* live threads poised
on conflicting operations. -/
def Config.RacingPair {α : Type} (c : Config α) : Prop :=
  ∃ i j f g, i ≠ j ∧ PendingOp c i f ∧ PendingOp c j g ∧ Conflict c.heap f g

/-- The pairwise analogue of `DataRaceFree`. Strictly stronger: it forbids a
configuration in which a race is *possible*, not only one in which a thread has
already been refused. -/
def PairwiseRaceFree {α : Type} (t : Result α) : Prop :=
  ∀ c, Reaches (init t) c → ¬ c.RacingPair

/-! ## λRust's compatibility table, for `Conflict`

Each row follows from the transition lemmas in `RustBelt.lean`, so the table is
derived twice over: from the operations, and now for the pairwise notion. -/

/-- `(ReadAcc, _), (ReadAcc, _) => True` — two readers never conflict. -/
theorem not_conflict_read_read (σ : RustHeap.{0}) (l : Loc) :
    ¬ Conflict σ (readAcquireF l) (readAcquireF l) := by
  rintro (⟨σ', hs, hn⟩ | ⟨σ', hs, hn⟩) <;>
    exact absurd (read_read_compatible σ σ' l hs) (by rw [hn]; simp)

/-- `(_, ScOrd), (_, ScOrd) => True` — two atomic stores never conflict. -/
theorem not_conflict_atomic_atomic (σ : RustHeap.{0}) (l : Loc) (v w : Val.{0}) :
    ¬ Conflict σ (storeAtF l v) (storeAtF l w) := by
  rintro (⟨σ', hs, hn⟩ | ⟨σ', hs, hn⟩)
  · exact absurd (atomic_atomic_compatible σ σ' l v w hs) (by rw [hn]; simp)
  · exact absurd (atomic_atomic_compatible σ σ' l w v hs) (by rw [hn]; simp)

/-- **write ∥ read is a race.** -/
theorem conflict_write_read (σ : RustHeap.{0}) (l : Loc) (v : Val.{0})
    (h : get? σ l = some (AccessState.reading 0, v)) :
    Conflict σ (writeAcquireF l) (readAcquireF l) := by
  obtain ⟨σ', hs⟩ : ∃ σ', writeAcquireF l σ = some σ' := by
    rcases hw : writeAcquireF l σ with _ | σ'
    · exact absurd ((writeAcquire_enabled σ l).mpr ⟨v, h⟩) (by rw [hw]; simp)
    · exact ⟨σ', rfl⟩
  exact .inl ⟨σ', hs, Option.not_isSome_iff_eq_none.mp (write_read_incompatible σ σ' l hs)⟩

/-- **write ∥ write is a race.** -/
theorem conflict_write_write (σ : RustHeap.{0}) (l : Loc) (v : Val.{0})
    (h : get? σ l = some (AccessState.reading 0, v)) :
    Conflict σ (writeAcquireF l) (writeAcquireF l) := by
  obtain ⟨σ', hs⟩ : ∃ σ', writeAcquireF l σ = some σ' := by
    rcases hw : writeAcquireF l σ with _ | σ'
    · exact absurd ((writeAcquire_enabled σ l).mpr ⟨v, h⟩) (by rw [hw]; simp)
    · exact ⟨σ', rfl⟩
  exact .inl ⟨σ', hs, Option.not_isSome_iff_eq_none.mp (write_write_incompatible σ σ' l hs)⟩

/-- **read ∥ write is a race** — the mirror, and the one
`Races.racesOn_writeAcquire` witnesses. -/
theorem conflict_read_write (σ : RustHeap.{0}) (l : Loc) (n : Nat) (v : Val.{0})
    (h : get? σ l = some (AccessState.reading n, v)) :
    Conflict σ (readAcquireF l) (writeAcquireF l) := by
  obtain ⟨σ', hs⟩ : ∃ σ', readAcquireF l σ = some σ' := by
    rcases hr : readAcquireF l σ with _ | σ'
    · exact absurd ((readAcquire_enabled σ l).mpr ⟨n, v, h⟩) (by rw [hr]; simp)
    · exact ⟨σ', rfl⟩
  exact .inl ⟨σ', hs, Option.not_isSome_iff_eq_none.mp (read_write_incompatible σ σ' l hs)⟩

/-! ## The missing premise, named

Everything above is unconditional. What follows is where the cooperative machine
stops being able to help. -/

/-- **The scheduling premise a preemptive machine gives for free.**

"Once thread `i`'s pending operation has run, a configuration is reachable in
which thread `j` is scheduled with *its* operation still pending and the heap
unchanged since."

λRust's machine satisfies this always: any thread may step next. This one does
not, because control moves only at `yield`. It is stated as a hypothesis rather
than assumed silently, and rather than being papered over by weakening the
conclusion. -/
def SchedulableAfter {α : Type} (t : Result α) (c : Config α) (i j : Nat) : Prop :=
  ∀ f g σ', PendingOp c i f → PendingOp c j g → f c.heap = some σ' →
    ∃ c', Reaches (init t) c' ∧ c'.heap = σ' ∧
      ∃ k, c'.focus = some (Result.vis (modifyEv g) k)

/-- One direction of the conflict, ruled out. The proof is short because all the
content is in the hypothesis: once `j` is scheduled at `σ'` with `g` pending and
`g σ' = none`, that configuration is `Faulty` outright. -/
theorem not_conflict_left_of_schedulable {α : Type} {t : Result α} {c : Config α}
    {i j : Nat} {f g : RustHeap.{0} → Option RustHeap.{0}}
    (hS : Safe t) (hf : PendingOp c i f) (hg : PendingOp c j g)
    (hsched : SchedulableAfter t c i j) :
    ¬ (∃ σ', f c.heap = some σ' ∧ g σ' = none) := by
  rintro ⟨σ', hfs, hgn⟩
  obtain ⟨c', hc', hheap, k, hfoc⟩ := hsched f g σ' hf hg hfs
  exact hS c' hc' ⟨_, hfoc, .inr ⟨g, k, rfl, by rw [hheap]; exact hgn⟩⟩

/-- **λRust's `safe_nonracing`, with its scheduling assumption made explicit.**

Read the hypothesis as "the scheduler can get to both threads". Supply it and
the pairwise statement follows; it is exactly what this machine cannot give. -/
theorem pairwiseRaceFree_of_safe {α : Type} {t : Result α} (hS : Safe t)
    (hsched : ∀ c, Reaches (init t) c → ∀ i j, i ≠ j → SchedulableAfter t c i j) :
    PairwiseRaceFree t := by
  rintro c hc ⟨i, j, f, g, hij, hf, hg, hconf⟩
  rcases hconf with h | h
  · exact not_conflict_left_of_schedulable hS hf hg (hsched c hc i j hij) h
  · exact not_conflict_left_of_schedulable hS hg hf (hsched c hc j i (Ne.symm hij)) h

/-! ## The gap, exhibited

`Vacuity.lean`'s `racer` is the program where the race *does* manifest: its
parent yields immediately after forking, so the child gets to take the write lock
and the parent is then refused. Five machine steps, and `Races.Config.Racing`
fires.

`starver` below is the same program with **one `yield` removed**. Nothing else
changes. Now the parent takes the lock, returns, and — because a returned thread
takes no step and `yield` is the only rule that moves the lock — the machine
stops with the child never scheduled. Its pending write is never attempted.

At the configuration reached just after the fork, the two definitions disagree,
and both halves of the disagreement are proved below. -/

/-- The parent: take the write lock and return. **No `yield`** — that is the
entire difference from `Vacuity.racer`. -/
noncomputable def starverParent : Result Nat :=
  Result.vis (modifyEv (writeAcquireF 0)) (fun _ => Result.ok 0)

/-- The child: also wants the write lock. It will never get to ask. -/
noncomputable def starverChild : Result Nat :=
  Result.vis (modifyEv (writeAcquireF 0)) (fun _ => Result.ok 1)

noncomputable def starver : Result Nat :=
  Result.vis (modifyEv setupF) (fun _ =>
    Result.vis forkEv (fun tag => match tag with
      | ConcE.Tags.cur => starverParent
      | ConcE.Tags.new => starverChild))

/-- Just after the fork: both threads poised on the same write lock, the parent
scheduled. Note `Step.fork` leaves `current` alone, so the parent still holds the
lock. -/
noncomputable def cStarve : Config Nat :=
  ⟨[Thread.alive starverParent, Thread.alive starverChild], 0, h0⟩

/-- Two steps: allocate, then fork. -/
theorem starve_reachable : Reaches (init starver) cStarve := by
  refine .tail (Step.heap (c := init starver) rfl setup_ok) ?_
  exact .tail (Step.fork (c := ⟨[Thread.alive _], 0, h0⟩) rfl) (.refl _)

/-- **λRust says: race.** Two distinct threads, both about to `writeAcquire` the
same location, and write ∥ write conflicts. -/
theorem cStarve_racingPair : cStarve.RacingPair :=
  ⟨0, 1, writeAcquireF 0, writeAcquireF 0, by decide, ⟨_, rfl⟩, ⟨_, rfl⟩,
   conflict_write_write h0 0 (Val.pack (0 : Nat)) g_h0_0⟩

/-- **We say: not yet.** The scheduled thread's operation is enabled — it
succeeds, taking `h0` to `h1` — so nothing is refused at this configuration and
`Races.Config.Racing` cannot hold. The race is real, but it is one `yield` away
from being observable, and that `yield` is not in the program. -/
theorem cStarve_scheduled_op_succeeds : writeAcquireF 0 cStarve.heap = some h1 :=
  wa_h0

/-- The disagreement, in one statement: a **reachable** configuration that the
pairwise notion calls a race and the manifested notion does not.

This is not a defect in either definition. It is the cost of a machine in which
control moves only at `yield`, and it is why `pairwiseRaceFree_of_safe` needs
`SchedulableAfter`: here the child is precisely *not* schedulable after the
parent's operation, because the parent returns instead of yielding. -/
theorem gap_witness :
    Reaches (init starver) cStarve ∧ cStarve.RacingPair ∧
      writeAcquireF 0 cStarve.heap ≠ none :=
  ⟨starve_reachable, cStarve_racingPair,
   by show writeAcquireF 0 h0 ≠ none; rw [wa_h0]; simp⟩

/-! ## Why the premise cannot simply be discharged

It is tempting to try to prove `SchedulableAfter` outright, and worth recording
why that fails, so the next person does not spend a day on it.

**Operationally.** Reaching a configuration in which `j` is scheduled requires a
`Step.yield`, which requires the thread *currently* holding the lock to be sitting
on a `yield` node. Nothing forces that: it may be mid-computation, may diverge,
or may return — and a returned non-main thread freezes the machine entirely.

**In Iris.** One might hope to read the premise off `SysInv` instead. `SysInv`
does carry an obligation for every live thread, but a non-scheduled thread's is
`readyObl = |={⊤,∅}=> runObl`, and *using* it spends `ownE ⊤`. The scheduled
thread has already spent that token. `ownE` is not duplicable, so at most one
thread's obligation can be opened at a configuration — which is precisely the big
lock doing its job. Two threads' pending operations cannot both be inspected.

Both routes fail for the same underlying reason, and it is a design decision
rather than a defect: **the cooperative machine and the atomicity-free
`wpi_open_invariant` are the same choice seen from two sides.** Making the
machine preemptive would discharge `SchedulableAfter` and break the big lock.
-/

end AeneasIris.Semantics
