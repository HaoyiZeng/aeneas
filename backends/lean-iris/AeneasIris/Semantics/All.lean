import AeneasIris.Semantics.Machine
import AeneasIris.Semantics.Invariant
import AeneasIris.Semantics.Preservation
import AeneasIris.Semantics.Soundness
import AeneasIris.Semantics.Progress
import AeneasIris.Semantics.Outcome
import AeneasIris.Semantics.Races
import AeneasIris.Semantics.Sequential
import AeneasIris.Semantics.Termination
import AeneasIris.Semantics.Adequacy
import AeneasIris.Semantics.Example
import AeneasIris.Semantics.Vacuity
import AeneasIris.Semantics.TacticIssue
import AeneasIris.Semantics.RustBelt
import AeneasIris.Semantics.PairwiseRaces

/-!
# An operational semantics for Aeneas' ITrees, and adequacy of `wpi`

Single entry point. Importing this gets the whole development, including
`TacticIssue.lean` — which used to be quarantined as `sorry`-tainted bug
evidence and is now a clean set of regression tests for the (fixed) `istep`
soundness bug.

## Why there is a hand-written machine

*Program Logics à la Carte* closes its HeapLang loop because `expr`, `prim_step`
and the denotation `⟦·⟧` all live in Coq, so `opsem_adequacy.v` can glue the two
ends. For Aeneas, `⟦·⟧` is the OCaml pipeline (LLBC → Lean) and LLBC's semantics
lives in Charon — **neither is in Lean**. No Lean theorem of the form "`wpi`
implies the Rust source's operational semantics is adequate" is possible; that
link is a trust assumption on Aeneas/Charon, exactly as it already is today.

So the semantics is *defined* at the ITree level, as in the paper's Islaris case
study (§7), which likewise has no separate source language. The ITree is not the
compiled artifact; it **is** the language.

## The files

| file | contents |
|---|---|
| `Machine` | `Config`, the five `Step` rules, `Reaches`/`ReachesN`, `Config.Faulty`, `Safe`, `MayReturn`, `SN`, `Terminates` |
| `Invariant` | `SysInv` — the heap plus one obligation per thread; `runObl` (holds the lock, mask `∅`) vs `readyObl` (waiting for it, mask `⊤`) |
| `Preservation` | the five Iris lemmas: no fault, one-step preservation (`.part` and a `▷`-free `.total` variant), initialisation, and reading the postcondition off |
| `Soundness` | `SoundGF` (a concrete `BundledGFunctors` with all four `GpreS`/`GhostMapG` instances), `sysInv_reachesN`, `safe_of_provable`, `post_of_provable` |
| `Progress` | `Config.WF`, `progress`, `Config.Halted.no_step`, `safe_stuck_iff_halted` — no reachable configuration wedges |
| `Outcome` | `reaches_halted`, `produces_result`, `exists_mayReturn` — safety plus termination gives a *result* |
| `Races` | `RacesOn`, `DataRaceFree`, and non-vacuity against the real `Heap.{read,write}Acquire_body` |
| `Sequential` | the paper's `Sequential` side condition, for the hand-assembled non-concurrent residual |
| `Termination` | the `.total` half; two lemmas still open |
| `Adequacy` | `ProvableSpec` and the two final theorems |
| `Example` | two concrete programs, end to end |
| `Vacuity` | the mirror of `Example`: programs that **are** unsafe, a configuration that **is** racing |
| `RustBelt` | the correspondence with λRust's heap model, one `↔` per row of its table |
| `PairwiseRaces` | λRust's pairwise race notion, and the one hypothesis this machine cannot discharge |
| `TacticIssue` | regression tests for a fixed `istep` soundness bug (safe to import; no `sorry`) |

## A browsable version

`Semantics/docs/gen.py` generates `Semantics/docs/semantics.html`: the effect
signature, the heap model beside λRust's, every operation's enabling condition,
the five machine rules as inference rules, the invariant, the race definition
and the theorems — with a closing section listing exactly what a reader should
check and what is known to be wrong.

Every Lean snippet on that page is **extracted from these sources at generation
time**, never transcribed, because a page whose purpose is "check the
definitions" is worthless if the code it shows can drift from the code that is
compiled. Regenerate with `python3 AeneasIris/Semantics/docs/gen.py` from the
`lean-iris` directory.

## Scheduling is forced, not chosen

`ownE ⊤` is linear, and `ConcH` spends it as `yield ↦ 🧱`, `fork`'s child
obligation ↦ `💰`, `endthread ↦ 🧾`. So at most one thread is inside a yield-free
region — which is why `wpi_open_invariant` needs no atomicity side condition:
"atomic" here means "yield-free", not "one step". Rust's atomics (`stepP; body`,
no yield) are genuinely atomic; a non-atomic access is
`readAcquire; yield; readRelease`, and the `yield` is exactly where interference
becomes observable.

`Termination.lean` makes this explicit a second time: its fragment index
`Option Nat` (where the lock is) splits `yield`'s `🧱 = |={∅,⊤}=> |={⊤,∅}=>` down
the middle into a *release* and an *acquire*. The index was not invented to make
an induction go through; it was already in the handler.

## What is proved

All of the following depend only on `[propext, Classical.choice, Quot.sound]` —
no `sorryAx`, no added axiom. One `wpi` triple gives, for **every** schedule:

* `adequacy_part` / `safe_of_provable` — never panics, never performs an
  undefined heap operation;
* `dataRaceFree_of_provable` — no data races, with `RacesOn` defined without
  mentioning stuckness (the operation fails at `σ` yet succeeds on a heap with
  the *same contents*, so only the access state can be to blame);
* `post_of_provable` — if the main thread returns, its value satisfies `φ`;
* `progress` + `Config.Halted.no_step` — every reachable configuration either
  steps or has legitimately halted, and `Halted` is *exactly* the successor-free
  set, so the disjunction is not a tautology;
* `reaches_halted` / `produces_result` — safety **and** termination together give
  a result; neither hypothesis is redundant (in the proof, the base case uses
  only `progress` and the recursive case only `SN`).

`Example.lean` walks the whole chain on real programs: `prog` (alloc, store,
load) yields `prog_returns_42' : ∃ v, MayReturn prog v ∧ v = 42`, unconditional
and Iris-free; `cprog` (spawn, yield) exercises `fork`, `yield` and `endthread`
with a named theorem each, so all five machine rules have a concrete witness.

`Vacuity.lean` supplies the other half of the argument, without which none of
the above means anything. Every theorem here has the form "**nothing bad
happens**", and such a statement is worth exactly as much as the badness it
excludes: if `Config.Faulty` were unsatisfiable, `Safe` would be true of every
program and `adequacy_part` would be a tautology — and `Example.lean` could not
reveal it, because it only ever proves the good side. So `Vacuity.lean` exhibits
`panicProg_unsafe` and `loadProg_unsafe` (both `Panics` and `StuckOn` separately
inhabited, faulting at `init` itself so the proofs are one constructor) and
`racingConfig_racing`. Together with `prog_spec`, **both sides of every
implication are inhabited.**

`Vacuity.lean` also settles race freedom the other way round: `racer` is a
five-step, two-thread program that genuinely races, and `racer_unprovable`
concludes that **no `wpi` triple exists for it, for any postcondition**. Race
freedom is therefore a consequence the logic enforces, not a coincidence of the
examples chosen.

## Known weaknesses

Recorded here rather than left to be discovered.

**A non-main thread sitting on `ret` freezes the machine.** `Config.focus`
returns the scheduled thread; a thread that has returned takes no `Step`, and
`yield` is the only rule that changes `current`. So if the scheduler hands the
lock to a thread that then returns, no rule applies and the configuration is
final — with other threads still alive and holding pending work. `Config.Halted`
classifies this as a legitimate halt (its `ok v` disjunct does not distinguish
the main thread), and `Outcome.lean` notes that the halting thread need not be
the main one, but not that live threads may be abandoned.

Rust's semantics is the opposite: a spawned thread that returns ends only
itself. The honest fix is a `Step` rule retiring a non-main returning thread,
exactly as `endthread` does; provable programs are unaffected either way,
because the logic already forces a forked child's postcondition to be `False`.

The consequence for the theorems: `Safe`, `Terminates` and `produces_result` are
weaker for an arbitrary `t` than they read, since a fault sitting behind a
returning child is unreachable only because the machine stops. This does not
affect anything proved about `ProvableSpec` programs, but it is a gap between
the machine and Rust and should be closed.

**Return types are restricted to `Type 0`.** `ProvableSpec`, `Config`, `Safe`
and everything downstream take `{α : Type}`, and `HeapGS.{0}` pins the heap at
universe 0. Rust functions returning a `Type 1` value — one quantifying over
types, say — are outside the statements as written. Nothing in the proofs
depends on the restriction; it is there because `Result`'s own universe
arithmetic (`Result (α : Type v) : Type (max v 1)`) makes the polymorphic
version noisy, and no example needed it.

**Two names for one definition.** `ProvableSpecOf` (`Soundness`) and
`ProvableSpec` (`Adequacy`) are the same notion; `dataRaceFree_of_provable`
takes the first, `adequacy_part` the second. Harmless but untidy — the
definition belongs upstream in `Invariant.lean`, with one name.

**`Sequential` is recorded, not derived.** See the note on
`rustSeq_sequential`: the sequential handler is hand-assembled rather than
obtained from `rustH` by deleting its `ConcH` summand.

## What is assumed

Exactly one thing: that the ITree Aeneas emits corresponds to the Rust source.
That is the pre-existing trust assumption, and it cannot be a Lean theorem.

Note also that `ProvableSpec` fixes a **pure** postcondition `⌜φ v⌝` — necessary,
because `fupd_plain_mask` needs `Plain`, and that instance exists only at
`HasLC.hasNoLC`. A consequence worth knowing: nothing is concluded about the
final heap, and clients may not use later credits. The paper's `heap_adequacy`
threads the state interpretation out; there is no `wp_invariance` analogue here.

## What is open

**Nothing.** `AeneasIris/Semantics/` contains no `sorry` and no `axiom`, and
both final theorems are clean:

```
'adequacy_part'  depends on axioms: [propext, Classical.choice, Quot.sound]
'adequacy_total' depends on axioms: [propext, Classical.choice, Quot.sound]
```

So `adequacy_total` holds too: a `wpi` triple at `.total` gives safety, race
freedom, the postcondition on return, **and** termination — no silent
divergence and no infinite execution, under every schedule.

The termination half was the hard part, and it went through two refutations
before it went through: `TP_app_l` and then `TPf_app`'s first form were both
*disproved* by counterexample before the right statements were found. The
lesson is recorded in `Termination.lean` and is worth repeating here — the
`Frag = List PThread × Option Nat` index, which carries the location of the big
lock, was not invented to make an induction close. It was already latent in
`ConcH`, whose `yield ↦ |={∅,⊤}=> |={⊤,∅}=>` is a release followed by an
acquire; `curMask` just names the two halves. Iris's `twptp_app` never had to
handle the cross terms because Iris's machine has no lock.

Three findings for the maintainer are recorded in the session notes rather than
here: `spawn_spec`'s registration style, the `unif_hint`-vs-`simp` gap in
`Effect.lean`, and — now fixed — the `istep` bug, whose regression tests live in
`TacticIssue.lean`.
-/
