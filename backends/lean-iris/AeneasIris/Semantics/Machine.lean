import Aeneas.Std.Primitives

/-!
# The machine: configurations, and the *signature* of the step relation

**This file deliberately contains no semantics.** It fixes the shape of the
operational model — what a configuration is, what can go wrong, what "safe" and
"returns" mean — so that the final theorem in `Semantics/Adequacy.lean` can be
read and checked before any of it is defined or proved.

## Why we have to define a machine at all

"Program Logics à la Carte" closes its HeapLang loop because `expr`, `prim_step`
*and* the denotation `⟦·⟧` all live in Coq, so `opsem_adequacy.v` can glue the
two ends together. For us `⟦·⟧` is the Aeneas pipeline (LLBC → Lean, in OCaml)
and LLBC's semantics lives in Charon — **neither is in Lean**. So no Lean theorem
of the form "`wpi` ⟹ the Rust source's operational semantics is adequate" is
possible; that link is a trust assumption on Aeneas/Charon, exactly as it already
is today.

What we *can* do — and what the paper's Islaris case study (§7) does for machine
code, which has no separate source language either — is **define the operational
semantics at the ITree level**. The ITree is not "the compiled artifact"; it *is*
the language.

## Scheduling is forced, not chosen

Threads may only switch at `yield`. This is not a modelling choice: `ownE ⊤` is
linear, and `ConcH` spends it as `yield ↦ 🧱`, `fork`'s child obligation ↦ `💰`,
`endthread ↦ 🧾`. Together these say **at most one thread is inside a yield-free
region at a time**, which is also why `wpi_open_invariant` needs no atomicity
side-condition: "atomic" in this logic means "yield-free", not "one step".

Consequently Rust's atomics (`cas` / `load_at` / `faa`, all of the form
`stepP; body` with no yield) are genuinely atomic, while a non-atomic access is
`readAcquire; yield; readRelease` — the `yield` is precisely the point at which
interference becomes observable.
-/

namespace AeneasIris.Semantics

open Aeneas.Data.Coinductive
open Aeneas.Std (Result RustEffect RustHeap Error Loc AccessState Cell Val
  FailE ConcE StepE StateE)

unseal Aeneas.Std.Result

universe u

/-! ## Events, named

Injections of the four summands of
`RustEffect = FailE ⊕ₑ ConcE ⊕ₑ StepE ⊕ₑ StateE RustHeap`.
`Aeneas.Std.RustEffect.fail` already exists; the other three do not. They are
`@[match_pattern]` so that the step relation can be written by pattern matching. -/

@[match_pattern] abbrev forkEv : RustEffect.I := .inr (.inl ConcE.I.fork)
@[match_pattern] abbrev yieldEv : RustEffect.I := .inr (.inl ConcE.I.yield)
@[match_pattern] abbrev endthreadEv : RustEffect.I := .inr (.inl ConcE.I.endthread)
@[match_pattern] abbrev stepEv : RustEffect.I := .inr (.inr (.inl StepE.I.step))

/-- The one state primitive: transform the heap, or be undefined. -/
@[match_pattern] abbrev modifyEv (f : RustHeap.{0} → Option RustHeap.{0}) :
    RustEffect.I :=
  .inr (.inr (.inr (StateE.I.modify f)))

/-! ## Configurations -/

/-- A thread. All threads of a program share one return type: `fork` is
Unix-style, so both arms are the *same* continuation `k : ConcE.O .fork → ITree E α`.

`dead` is a tombstone rather than a removal so that thread indices — and hence
`Config.current` — stay stable across an `endthread`. -/
inductive Thread (α : Type) where
  /-- Still running. -/
  | alive (t : Result α)
  /-- Ended by `endthread`. -/
  | dead

/-- The default thread is `dead`, **not** `alive default`.

`deriving Inhabited` would pick the first constructor, and `Result`'s own default
is `Result.fail .panic` — so the derived default thread would be one that is
about to panic, i.e. a `Config.Faulty` witness. Nothing currently reads a
`Thread` out of thin air, but a default value that is *itself* the thing every
theorem here rules out is a trap worth disarming rather than documenting. -/
instance {α : Type} : Inhabited (Thread α) := ⟨.dead⟩

/-- A machine configuration.

`current` is the thread holding the "big lock", i.e. the one inside a yield-free
region. Only `current` may take a step; `yield` is what lets `current` change. -/
structure Config (α : Type) where
  threads : List (Thread α)
  /-- Index into `threads` of the thread that holds the big lock. -/
  current : Nat
  heap : RustHeap.{0}

/-- Thread `0` is the main thread; its return value is the program's result.

The initial heap is empty, which is the situation for a Rust `main`. Starting
from an arbitrary `σ₀` is a routine generalisation: the precondition of
`ProvableSpec` would then hand the client the points-to assertions for `σ₀`
instead of `emp`. -/
def init {α : Type} (t : Result α) : Config α :=
  { threads := [.alive t], current := 0, heap := ∅ }

/-- The thread currently holding the lock, if it is alive. -/
def Config.focus {α : Type} (c : Config α) : Option (Result α) :=
  match c.threads[c.current]? with
  | some (.alive t) => some t
  | _ => none

/-! ## Stepping helpers -/

/-- Overwrite the scheduled thread. -/
def Config.setFocus {α : Type} (c : Config α) (t : Result α) : Config α :=
  { c with threads := c.threads.set c.current (.alive t) }

/-- Mark the scheduled thread dead. -/
def Config.kill {α : Type} (c : Config α) : Config α :=
  { c with threads := c.threads.set c.current .dead }

/-- Thread `j` exists and is still running, so control may pass to it. -/
def Config.Alive {α : Type} (c : Config α) (j : Nat) : Prop :=
  ∃ t, c.threads[j]? = some (.alive t)

/-! ## The step relation

Only `c.current` — the thread holding the big lock — may fire, and the lock
changes hands only at `yield` and `endthread`. Four nodes have **no** rule, and
the difference between them is the whole content of adequacy:

* `ret v` — the thread has finished;
* `div` — silent divergence (permitted at `.part`, excluded at `.total`);
* `vis (fail e) k` — **a panic**, and
* `vis (modify f) k` with `f heap = none` — **an undefined heap operation**.

The last two are `Config.Faulty`; the first two are not. Note that `f heap = none`
is a *layered* notion of undefined behaviour: `AccessState = writing | reading n`
is λRust's read/write state machine and `writeAcquire` demands `reading 0`, so
two concurrent `store_na`s get stuck there — data-race freedom is an instance of
"the machine does not get stuck", not a separate obligation. A type-mismatched
`load_at` (`v.1 = T` fails) is stuck for the same reason.

When the last live thread executes `endthread` there is no `j` to pass control
to and the machine simply stops. That is not a fault; it is the paper's
`KillLastThread` case (footnote 7), and it needs no separate rule here because
`Faulty` does not mention it. -/
inductive Step {α : Type} : Config α → Config α → Prop where
  /-- A `step` marker: pure bookkeeping, the heap is untouched. At `.part` this
  is the node whose handler issues the `▷`, i.e. the entry point for Löb. -/
  | tick {c : Config α} {k} :
      c.focus = some (Result.vis stepEv k) →
      Step c (c.setFocus (k PUnit.unit))
  /-- The one state primitive. Note the continuation receives the **old** heap:
  `StateE.O (.modify f) = S`, and `stateH` hands `Ψ s` for the pre-state `s`. -/
  | heap {c : Config α} {f k σ'} :
      c.focus = some (Result.vis (modifyEv f) k) →
      f c.heap = some σ' →
      Step c { c.setFocus (k c.heap) with heap := σ' }
  /-- The only scheduling point. Control may pass to any live thread, including
  the current one. -/
  | yield {c : Config α} {k j} :
      c.focus = some (Result.vis yieldEv k) →
      (c.setFocus (k PUnit.unit)).Alive j →
      Step c { c.setFocus (k PUnit.unit) with current := j }
  /-- Unix-style fork: the *same* continuation is resumed twice, with different
  tags. The child is appended but not scheduled — it becomes eligible at the
  next `yield`, which is what makes `wpi_fork` hand it its obligation under
  `|={⊤,∅}=>`. -/
  | fork {c : Config α} {k} :
      c.focus = some (Result.vis forkEv k) →
      Step c { threads := (c.threads.set c.current (.alive (k ConcE.Tags.cur)))
                            ++ [.alive (k ConcE.Tags.new)],
               current := c.current,
               heap := c.heap }
  /-- End the thread and hand the lock on. -/
  | endthread {c : Config α} {k j} :
      c.focus = some (Result.vis endthreadEv k) →
      c.kill.Alive j →
      Step c { c.kill with current := j }

/-- Reflexive-transitive closure of `Step`. Spelled out rather than taken from
Mathlib to keep this file's dependencies to `Aeneas.Std.Primitives`. -/
inductive Reaches {α : Type} : Config α → Config α → Prop where
  | refl (c : Config α) : Reaches c c
  | tail {c₁ c₂ c₃ : Config α} : Step c₁ c₂ → Reaches c₂ c₃ → Reaches c₁ c₃

/-- `Reaches`, carrying the number of steps.

Adequacy is step-indexed: `n` machine steps are paid for by the `n` `▷`s of
`|={∅}▷=>^[n]`, which `step_fupdN_soundness` then discharges. So the proof needs
the count, while the statement of the final theorem does not. -/
inductive ReachesN {α : Type} : Nat → Config α → Config α → Prop where
  | refl (c : Config α) : ReachesN 0 c c
  | tail {n : Nat} {c₁ c₂ c₃ : Config α} :
      Step c₁ c₂ → ReachesN n c₂ c₃ → ReachesN (n + 1) c₁ c₃

theorem Reaches.toReachesN {α : Type} {c c' : Config α} (h : Reaches c c') :
    ∃ n, ReachesN n c c' := by
  induction h with
  | refl c => exact ⟨0, .refl c⟩
  | tail hs _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, .tail hs hn⟩

/-! ## What can go wrong -/

/-- The thread is about to panic: it sits on a `fail` node. -/
def Panics {α : Type} (t : Result α) : Prop :=
  ∃ (e : Error) (k : RustEffect.O (Aeneas.Std.RustEffect.fail e) → Result α),
    t = Result.vis (Aeneas.Std.RustEffect.fail e) k

/-- The thread is about to perform a heap operation that is undefined at the
current heap: out of bounds, a type mismatch, or a data race. -/
def StuckOn {α : Type} (σ : RustHeap.{0}) (t : Result α) : Prop :=
  ∃ (f : RustHeap.{0} → Option RustHeap.{0}) (k : RustEffect.O (modifyEv f) → Result α),
    t = Result.vis (modifyEv f) k ∧ f σ = none

/-- The thread has silently diverged. Permitted under partial correctness,
excluded under total correctness. -/
def Diverges {α : Type} (t : Result α) : Prop := t = Result.div

/-- A configuration in which the scheduled thread is about to do something the
machine forbids. This is exactly what adequacy rules out. -/
def Config.Faulty {α : Type} (c : Config α) : Prop :=
  ∃ t, c.focus = some t ∧ (Panics t ∨ StuckOn c.heap t)

/-- The scheduled thread has silently diverged. -/
def Config.Diverging {α : Type} (c : Config α) : Prop :=
  ∃ t, c.focus = some t ∧ Diverges t

/-! ## The properties the final theorem delivers -/

/-- No execution from `t` ever reaches a panicking or stuck configuration.

Because `yield` may hand control to *any* live thread, quantifying over all
reachable configurations quantifies over all schedules; a thread that could
fault under some schedule is the focus of some reachable configuration. -/
def Safe {α : Type} (t : Result α) : Prop :=
  ∀ c, Reaches (init t) c → ¬ c.Faulty

/-- Some execution of `t` has the main thread **scheduled and returning** `v`.

The `c.current = 0` conjunct is not cosmetic. A thread's postcondition can only
be read off while it holds the big lock: an unscheduled thread's obligation is
`|={⊤,∅}=> …`, an implication *waiting for* `ownE ⊤`, and that token lives
inside whichever thread is currently running. Concretely, a main thread that
does `yield` and only then returns sits at `ret v` while another thread runs,
and at that configuration `φ v` — though true — is not derivable. It becomes
derivable as soon as the scheduler hands the lock back, which it may always do,
so nothing is lost: the observation is simply made at a configuration where the
main thread is scheduled.

This is the analogue of Iris's `wptp_postconditions`, which likewise reads
postconditions off at mask `⊤`. -/
def MayReturn {α : Type} (t : Result α) (v : α) : Prop :=
  ∃ c, Reaches (init t) c ∧ c.current = 0 ∧ c.focus = some (Result.ok v)

/-- No infinite execution from `c`. (`Acc` of the reversed relation.) -/
def SN {α : Type} (c : Config α) : Prop :=
  Acc (fun c₂ c₁ => Step c₁ c₂) c

/-- Every execution of `t` terminates, and no thread silently diverges. -/
def Terminates {α : Type} (t : Result α) : Prop :=
  ∀ c, Reaches (init t) c → SN c ∧ ¬ c.Diverging

end AeneasIris.Semantics
