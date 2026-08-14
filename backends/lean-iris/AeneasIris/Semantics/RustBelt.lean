import AeneasIris.Semantics.Races

/-!
# The correspondence with RustBelt's λRust

The heap model is not ours: `AccessState` is λRust's `lock_state`, and every
heap operation's enabling condition is one row of λRust's table. This file
states the correspondence as **machine-checked theorems**, one per operation,
so that "we follow RustBelt" is something a reader can verify rather than take
on trust.

## λRust, for reference

`lambda-rust/theories/lang/lang.v`:

```coq
Inductive lock_state := WSt | RSt (n : nat).
Definition state := gmap loc (lock_state * val).
```

and `lambda-rust/theories/lang/races.v`, `next_access_head_reducible_state` —
the enabling condition of each access, which that file calls "a crucial
definition; if we forget to sync it with head_step, the results proven here are
worthless":

```coq
match a with
| (ReadAcc, ScOrd | Na1Ord) => ∃ v n, σ !! l = Some (RSt n, v)
| (ReadAcc, Na2Ord)         => ∃ v n, σ !! l = Some (RSt (S n), v)
| (WriteAcc, ScOrd | Na1Ord)=> ∃ v,   σ !! l = Some (RSt 0, v)
| (WriteAcc, Na2Ord)        => ∃ v,   σ !! l = Some (WSt, v)
| (FreeAcc, _)              => ∃ v ls, σ !! l = Some (ls, v)
end
```

λRust splits a non-atomic access into two steps, `Na1Ord` then `Na2Ord`; we
split it into `readAcquire`/`readRelease` and `writeAcquire`/`writeRelease`,
which is the same split under different names. The dictionary is:

| λRust | here |
|---|---|
| `RSt n` | `AccessState.reading n` |
| `WSt` | `AccessState.writing` |
| `Read Na1Ord` | `readAcquire` |
| `Read Na2Ord` | `readRelease` |
| `Write Na1Ord` | `writeAcquire` |
| `Write Na2Ord` | `writeRelease` |
| `Read ScOrd` | `load_at` |
| `Write ScOrd` | `store_at` |
| `CAS` | `cas` |

## Two things λRust does that we do differently

**Where the interleaving point is.** λRust is a small-step language, so any
thread may be scheduled between the two halves of a non-atomic access. We have
no scheduler outside the program, so `load_na` and `store_na` place an explicit
`yield` between acquire and release (`Effects/Heap.lean`). The effect is the
same — the middle of a non-atomic access is exactly where another thread may
observe it — but here it is visible in the ITree rather than in a scheduler.

**How a race is defined.** This is the substantive difference and it is worth
stating plainly; see the section at the bottom.
-/

namespace AeneasIris.Semantics.RustBelt

open Iris
open Aeneas.Data.Coinductive
open Aeneas.Std (Result RustEffect RustHeap Loc AccessState Val Cell)
open Std.PartialMap
open AeneasIris.Semantics
open scoped Aeneas.Std

unseal Aeneas.Std.Result

variable {E : Effect.{1}} [Aeneas.Std.StateE RustHeap.{0} -< E]

/-! ## The state transformers

Each is proved by `rfl` to be the transformer inside the corresponding
`Heap.*_body`, so the theorems below are about the real operations. This is the
same discipline as `Races.lean`'s `writeAcquireF_eq` / `readAcquireF_eq`, which
cover the other two. -/

/-- `readRelease`'s transformer. -/
def readReleaseF (l : Loc) : RustHeap.{0} → Option RustHeap.{0} := fun σ =>
  match get? σ l with
  | some (AccessState.reading (n + 1), v) => some (insert σ l (AccessState.reading n, v))
  | _ => none

theorem readReleaseF_eq (l : Loc) :
    (AeneasIris.Heap.readRelease_body (E := Aeneas.Std.RustEffect) l :
        ITree Aeneas.Std.RustEffect PUnit.{1})
      = AeneasIris.Heap.act' (S := RustHeap.{0}) (readReleaseF l) (fun _ => PUnit.unit) :=
  rfl

/-- `writeRelease`'s transformer. -/
def writeReleaseF (l : Loc) (v : Val.{0}) : RustHeap.{0} → Option RustHeap.{0} := fun σ =>
  match get? σ l with
  | some (AccessState.writing, _) => some (insert σ l (AccessState.reading 0, v))
  | _ => none

theorem writeReleaseF_eq (l : Loc) (v : Val.{0}) :
    (AeneasIris.Heap.writeRelease_body (E := Aeneas.Std.RustEffect) l v :
        ITree Aeneas.Std.RustEffect PUnit.{1})
      = AeneasIris.Heap.act' (S := RustHeap.{0}) (writeReleaseF l v) (fun _ => PUnit.unit) :=
  rfl

/-- `store_at`'s transformer — the sequentially consistent write. -/
def storeAtF (l : Loc) (v : Val.{0}) : RustHeap.{0} → Option RustHeap.{0} := fun σ =>
  match get? σ l with
  | some (AccessState.reading 0, _) => some (insert σ l (AccessState.reading 0, v))
  | _ => none

theorem storeAtF_eq (l : Loc) (v : Val.{0}) :
    (AeneasIris.Heap.store_body (E := Aeneas.Std.RustEffect) l v :
        ITree Aeneas.Std.RustEffect PUnit.{1})
      = AeneasIris.Heap.act' (S := RustHeap.{0}) (storeAtF l v) (fun _ => PUnit.unit) :=
  rfl

/-- `free`'s transformer. -/
def freeF (l : Loc) : RustHeap.{0} → Option RustHeap.{0} := fun σ =>
  match get? σ l with
  | some (AccessState.reading 0, _) => some (delete σ l)
  | _ => none

theorem freeF_eq (l : Loc) :
    (AeneasIris.Heap.free_body (E := Aeneas.Std.RustEffect) l :
        ITree Aeneas.Std.RustEffect PUnit.{1})
      = AeneasIris.Heap.act' (S := RustHeap.{0}) (freeF l) (fun _ => PUnit.unit) :=
  rfl

/-! ## One theorem per row of λRust's table

Each says: the operation is enabled at `σ` **exactly** when λRust's condition
holds. `↔`, not `→`: an operation that were enabled more often would permit
races, and one enabled less often would make the machine stuck where λRust is
not, so both directions carry weight. -/

/-- `(ReadAcc, Na1Ord)` — `∃ v n, σ !! l = Some (RSt n, v)`. -/
theorem readAcquire_enabled (σ : RustHeap.{0}) (l : Loc) :
    (readAcquireF l σ).isSome ↔ ∃ n v, get? σ l = some (AccessState.reading n, v) := by
  constructor
  · intro h
    rcases hg : get? σ l with _ | ⟨st, v⟩
    · rw [readAcquireF, hg] at h; exact absurd h (by simp)
    · cases st with
      | writing => rw [readAcquireF, hg] at h; exact absurd h (by simp)
      | reading n => exact ⟨n, v, rfl⟩
  · rintro ⟨n, v, hg⟩; simp only [readAcquireF, hg]; rfl

/-- `(ReadAcc, Na2Ord)` — `∃ v n, σ !! l = Some (RSt (S n), v)`. The `S n` is
the point: releasing a read you do not hold has no transition. -/
theorem readRelease_enabled (σ : RustHeap.{0}) (l : Loc) :
    (readReleaseF l σ).isSome ↔ ∃ n v, get? σ l = some (AccessState.reading (n + 1), v) := by
  constructor
  · intro h
    rcases hg : get? σ l with _ | ⟨st, v⟩
    · rw [readReleaseF, hg] at h; exact absurd h (by simp)
    · cases st with
      | writing => rw [readReleaseF, hg] at h; exact absurd h (by simp)
      | reading n =>
        cases n with
        | zero => rw [readReleaseF, hg] at h; exact absurd h (by simp)
        | succ k => exact ⟨k, v, rfl⟩
  · rintro ⟨n, v, hg⟩; simp only [readReleaseF, hg]; rfl

/-- `(WriteAcc, Na1Ord)` — `∃ v, σ !! l = Some (RSt 0, v)`. **`0`, not `n`**:
this is the row that makes write-∥-read a race. -/
theorem writeAcquire_enabled (σ : RustHeap.{0}) (l : Loc) :
    (writeAcquireF l σ).isSome ↔ ∃ v, get? σ l = some (AccessState.reading 0, v) := by
  constructor
  · intro h
    rcases hg : get? σ l with _ | ⟨st, v⟩
    · rw [writeAcquireF, hg] at h; exact absurd h (by simp)
    · cases st with
      | writing => rw [writeAcquireF, hg] at h; exact absurd h (by simp)
      | reading n =>
        cases n with
        | zero => exact ⟨v, rfl⟩
        | succ k => rw [writeAcquireF, hg] at h; exact absurd h (by simp)
  · rintro ⟨v, hg⟩; simp only [writeAcquireF, hg]; rfl

/-- `(WriteAcc, Na2Ord)` — `∃ v, σ !! l = Some (WSt, v)`. -/
theorem writeRelease_enabled (σ : RustHeap.{0}) (l : Loc) (w : Val.{0}) :
    (writeReleaseF l w σ).isSome ↔ ∃ v, get? σ l = some (AccessState.writing, v) := by
  constructor
  · intro h
    rcases hg : get? σ l with _ | ⟨st, v⟩
    · rw [writeReleaseF, hg] at h; exact absurd h (by simp)
    · cases st with
      | writing => exact ⟨v, rfl⟩
      | reading n => rw [writeReleaseF, hg] at h; exact absurd h (by simp)
  · rintro ⟨v, hg⟩; simp only [writeReleaseF, hg]; rfl

/-- `(WriteAcc, ScOrd)` — `∃ v, σ !! l = Some (RSt 0, v)`. An atomic store still
requires no concurrent reader; atomics are only compatible with *other atomics*.
-/
theorem storeAt_enabled (σ : RustHeap.{0}) (l : Loc) (w : Val.{0}) :
    (storeAtF l w σ).isSome ↔ ∃ v, get? σ l = some (AccessState.reading 0, v) := by
  constructor
  · intro h
    rcases hg : get? σ l with _ | ⟨st, v⟩
    · rw [storeAtF, hg] at h; exact absurd h (by simp)
    · cases st with
      | writing => rw [storeAtF, hg] at h; exact absurd h (by simp)
      | reading n =>
        cases n with
        | zero => exact ⟨v, rfl⟩
        | succ k => rw [storeAtF, hg] at h; exact absurd h (by simp)
  · rintro ⟨v, hg⟩; simp only [storeAtF, hg]; rfl

/-! ## `cas`, the subtlest three rows

λRust splits compare-and-swap into three `head_step` rules, and the split is
easy to get wrong because it is *not* along the obvious line:

```coq
| CasSucS   : σ !! l = Some (RSt 0, litl) → lit_eq  lit1 litl → (* writes *)
| CasFailS  : σ !! l = Some (RSt n, litl) → lit_neq lit1 litl → (* only reads *)
| CasStuckS : σ !! l = Some (RSt n, litl) → 0 < n → lit_eq lit1 litl → (* stuck *)
```

A **failed** CAS is only a read, so it is enabled with any number of concurrent
readers (`RSt n`). A **successful** one is a write, so with a reader present it
is *stuck* — that is `CasStuckS`, and it is a genuine race.

These three are the rows most likely to drift from the implementation, so they
get theorems rather than a table entry. -/

/-- `cas`'s transformer. -/
noncomputable def casF (l : Loc) (old new : Val.{0}) :
    RustHeap.{0} → Option RustHeap.{0} := fun σ =>
  match get? σ l with
  | some (AccessState.reading 0, v) =>
      some (if v = old then insert σ l (AccessState.reading 0, new) else σ)
  | some (AccessState.reading (_ + 1), v) =>
      if v = old then none else some σ
  | _ => none

theorem casF_eq (l : Loc) (old new : Val.{0}) :
    (AeneasIris.Heap.cas_body (E := Aeneas.Std.RustEffect) l old new :
        ITree Aeneas.Std.RustEffect Bool)
      = AeneasIris.Heap.act' (S := RustHeap.{0}) (casF l old new)
          (fun σ => match get? σ l with
            | some (_, v) => v = old
            | none => false) :=
  rfl

/-- **`CasSucS`** — with no concurrent reader, `cas` is always enabled. -/
theorem cas_enabled_unlocked (σ : RustHeap.{0}) (l : Loc) (old new v : Val.{0})
    (h : get? σ l = some (AccessState.reading 0, v)) :
    (casF l old new σ).isSome := by
  simp only [casF, h]
  cases hv : decide (v = old) <;> rfl

/-- **`CasFailS`** — a *failing* CAS is only a read, so concurrent readers do not
block it. This is the row that would be lost by requiring `reading 0`
throughout. -/
theorem cas_enabled_readers_of_ne (σ : RustHeap.{0}) (l : Loc) (old new v : Val.{0})
    (n : Nat) (h : get? σ l = some (AccessState.reading (n + 1), v)) (hne : v ≠ old) :
    (casF l old new σ).isSome := by
  simp only [casF, h, if_neg hne]; rfl

/-- **`CasStuckS`** — a *succeeding* CAS is a write, so a concurrent reader makes
it stuck. This is a data race, and it is why the `cas` rows cannot be summarised
as "requires `reading 0`". -/
theorem cas_stuck_readers_of_eq (σ : RustHeap.{0}) (l : Loc) (old new v : Val.{0})
    (n : Nat) (h : get? σ l = some (AccessState.reading (n + 1), v)) (heq : v = old) :
    casF l old new σ = none := by
  simp only [casF, h, if_pos heq]

/-- And, as everywhere else, a cell being written blocks it outright. -/
theorem cas_stuck_writing (σ : RustHeap.{0}) (l : Loc) (old new v : Val.{0})
    (h : get? σ l = some (AccessState.writing, v)) :
    casF l old new σ = none := by
  simp only [casF, h]

/-! ## λRust's compatibility table, as transitions

`races.v` states which pairs of accesses do *not* race:

```coq
Definition nonracing_accesses (a1 a2 : access_kind * order) : Prop :=
  match a1, a2 with
  | (_, ScOrd), (_, ScOrd) => True
  | (ReadAcc, _), (ReadAcc, _) => True
  | _, _ => False
  end.
```

Here that table is not a definition but a *consequence* of the transitions: two
accesses are compatible exactly when performing one leaves the other enabled.
The four theorems below are that table, row by row. -/

/-- **read ∥ read is not a race.** After one reader acquires, another still can:
`reading n → reading (n+1)` is available for every `n`. This is λRust's
`(ReadAcc, _), (ReadAcc, _) => True`. -/
theorem read_read_compatible (σ σ' : RustHeap.{0}) (l : Loc)
    (h : readAcquireF l σ = some σ') : (readAcquireF l σ').isSome := by
  obtain ⟨n, v, hg⟩ := (readAcquire_enabled σ l).mp (by rw [h]; rfl)
  refine (readAcquire_enabled σ' l).mpr ⟨n + 1, v, ?_⟩
  rw [readAcquireF, hg] at h
  rw [← Option.some.inj h, Std.get?_insert_eq (rfl : l = l)]

/-- **write ∥ read is a race.** After a writer acquires, no reader can:
`writing` has no `readAcquire` transition. -/
theorem write_read_incompatible (σ σ' : RustHeap.{0}) (l : Loc)
    (h : writeAcquireF l σ = some σ') : ¬ (readAcquireF l σ').isSome := by
  intro hcon
  obtain ⟨v, hg⟩ := (writeAcquire_enabled σ l).mp (by rw [h]; rfl)
  obtain ⟨n, w, hg'⟩ := (readAcquire_enabled σ' l).mp hcon
  rw [writeAcquireF, hg] at h
  rw [← Option.some.inj h, Std.get?_insert_eq (rfl : l = l)] at hg'
  exact absurd hg' (by simp)

/-- **write ∥ write is a race**, for the same reason. -/
theorem write_write_incompatible (σ σ' : RustHeap.{0}) (l : Loc)
    (h : writeAcquireF l σ = some σ') : ¬ (writeAcquireF l σ').isSome := by
  intro hcon
  obtain ⟨v, hg⟩ := (writeAcquire_enabled σ l).mp (by rw [h]; rfl)
  obtain ⟨w, hg'⟩ := (writeAcquire_enabled σ' l).mp hcon
  rw [writeAcquireF, hg] at h
  rw [← Option.some.inj h, Std.get?_insert_eq (rfl : l = l)] at hg'
  exact absurd hg' (by simp)

/-- **read ∥ write is a race**, the mirror of `write_read_incompatible`: a
reader in progress blocks a writer. This is the row that
`Races.racesOn_writeAcquire` witnesses. -/
theorem read_write_incompatible (σ σ' : RustHeap.{0}) (l : Loc)
    (h : readAcquireF l σ = some σ') : ¬ (writeAcquireF l σ').isSome := by
  intro hcon
  obtain ⟨n, v, hg⟩ := (readAcquire_enabled σ l).mp (by rw [h]; rfl)
  obtain ⟨w, hg'⟩ := (writeAcquire_enabled σ' l).mp hcon
  rw [readAcquireF, hg] at h
  rw [← Option.some.inj h, Std.get?_insert_eq (rfl : l = l)] at hg'
  exact absurd hg' (by simp)

/-- **atomic ∥ atomic is not a race.** An atomic store leaves the cell in
`reading 0`, where every atomic operation is enabled. This is λRust's
`(_, ScOrd), (_, ScOrd) => True`, and it is why `store_at` needs no `yield`:
the whole operation is a single machine step. -/
theorem atomic_atomic_compatible (σ σ' : RustHeap.{0}) (l : Loc) (v w : Val.{0})
    (h : storeAtF l v σ = some σ') : (storeAtF l w σ').isSome := by
  obtain ⟨u, hg⟩ := (storeAt_enabled σ l v).mp (by rw [h]; rfl)
  refine (storeAt_enabled σ' l w).mpr ⟨v, ?_⟩
  rw [storeAtF, hg] at h
  rw [← Option.some.inj h, Std.get?_insert_eq (rfl : l = l)]

/-! ## `free` is `FreeAcc`, and races with everything

λRust's row is `(FreeAcc, _) => ∃ v ls, σ !! l = Some (ls, v)` — free is enabled
whenever the location exists, in *any* lock state, and `races.v` then rules out
racing with it separately (`next_access_head_Free_concurent_step`, which derives
`False` from a free concurrent with any other access).

We are stricter: `free` requires `reading 0`, so freeing a location that another
thread is reading or writing is *stuck*, and therefore already excluded by
`Safe`. The two designs agree on which programs are accepted; ours needs no
separate argument, at the cost of a `free` that is enabled less often than
λRust's. -/

theorem free_enabled (σ : RustHeap.{0}) (l : Loc) :
    (freeF l σ).isSome ↔ ∃ v, get? σ l = some (AccessState.reading 0, v) := by
  constructor
  · intro h
    rcases hg : get? σ l with _ | ⟨st, v⟩
    · rw [freeF, hg] at h; exact absurd h (by simp)
    · cases st with
      | writing => rw [freeF, hg] at h; exact absurd h (by simp)
      | reading n =>
        cases n with
        | zero => exact ⟨v, rfl⟩
        | succ k => rw [freeF, hg] at h; exact absurd h (by simp)
  · rintro ⟨v, hg⟩; simp only [freeF, hg]; rfl

/-- Use-after-free is caught as a race by the same mechanism: a reader in
progress blocks the free. -/
theorem read_free_incompatible (σ σ' : RustHeap.{0}) (l : Loc)
    (h : readAcquireF l σ = some σ') : ¬ (freeF l σ').isSome := by
  intro hcon
  obtain ⟨n, v, hg⟩ := (readAcquire_enabled σ l).mp (by rw [h]; rfl)
  obtain ⟨w, hg'⟩ := (free_enabled σ' l).mp hcon
  rw [readAcquireF, hg] at h
  rw [← Option.some.inj h, Std.get?_insert_eq (rfl : l = l)] at hg'
  exact absurd hg' (by simp)

/-! ## How a race is defined — the substantive difference

λRust defines a race **pairwise over the thread pool** (`races.v`):

```coq
Definition nonracing_accesses (a1 a2 : access_kind * order) : Prop :=
  match a1, a2 with
  | (_, ScOrd), (_, ScOrd) => True
  | (ReadAcc, _), (ReadAcc, _) => True
  | _, _ => False
  end.

Definition nonracing_threadpool (el : list expr) (σ : state) : Prop :=
  ∀ l a1 a2, next_accesses_threadpool el σ a1 a2 l → nonracing_accesses a1 a2.
```

Two threads, each *about to* touch the same location with an incompatible pair
of access kinds. `Races.RacesOn` instead looks at the **scheduled** thread and
asks whether it is stuck for an access-state reason. λRust's is a *potential*
race, ours a *manifested* one.

On programs built from this API they usually coincide, because of the `yield`
inside every non-atomic access: schedule one of the two threads, let it acquire,
yield to the other, and the other is stuck. `DataRaceFree` quantifies over all
reachable configurations and `yield` may pass control to any live thread, so
that schedule is reachable.

**Two places where they genuinely differ.** Both are weakenings on our side, and
both are recorded here rather than left to be discovered.

1. *At a single configuration.* λRust flags "both threads about to write, neither
   stuck yet"; we do not, until one has acquired. A configuration-local statement
   is not what `DataRaceFree` says.

2. *When the racing threads are never scheduled.* The argument above needs the
   **currently scheduled** thread to reach a `yield`. If it diverges, or returns —
   which freezes the machine, since a returned thread takes no step and `yield` is
   the only rule that changes `current` — then two parked threads with
   incompatible pending accesses are never scheduled, no configuration is ever
   `Config.Racing`, and `DataRaceFree` holds while λRust's
   `nonracing_threadpool` fails.

So `DataRaceFree` is a property of *executions*; λRust's is a property of
*configurations*, and a latent race is invisible to the first. Closing the gap
would need either the `Step` rule that retires a non-main returning thread (see
`All.lean`'s known weaknesses) or a pairwise race predicate proved directly from
`SysInv` — and the latter runs into the big lock, since extracting information
about a *non-scheduled* thread's obligation would require spending `ownE ⊤` a
second time. -/

end AeneasIris.Semantics.RustBelt
