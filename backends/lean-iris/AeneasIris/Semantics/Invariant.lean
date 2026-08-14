import AeneasIris.Rust
import AeneasIris.Semantics.Machine

/-!
# The system invariant

The bridge between a machine configuration and Iris resources. Everything here
is a *definition*; the lemmas that use it live in `Semantics/Preservation.lean`
and `Semantics/Soundness.lean`.

## Where `ownE ⊤` lives

This is the whole design, so it is worth stating explicitly.

`wpi_mask GF H m t Φ ⊤` unfolds to `|={⊤,∅}=> wpi GF H m t (fun v => |={∅,⊤}=> Φ v)`.
So a thread that has **not** been scheduled is an implication *waiting for*
`ownE ⊤`, and a thread that **is** scheduled has already consumed it: the token
sits inside its `wpi`, in the closing update its postcondition carries. Since
`ownE ⊤` is linear, at most one thread can be in the second state — which is
exactly the big lock that `Config.current` records, and exactly why
`wpi_open_invariant` needs no atomicity side condition.

The handoff is visible in `ConcH`:

* `yield ↦ 🧱 (Ψ ()) = |={∅,⊤}=> |={⊤,∅}=> Ψ ()` — release the token, then take
  it back. In the adequacy proof the two halves are split: the first releases it
  into the ambient, the second is re-supplied by whichever thread is scheduled
  next (possibly the same one).
* `endthread ↦ 🧾 True = |={∅,⊤}=> True` — release it and never take it back.
* `fork ↦ Ψ .cur ∗ Ψs .new`, with `wpiAcc` setting `Ψs a = |={⊤,∅}=> …` — the
  parent keeps the token, the child is created *waiting for* one.

Consequently `SysInv` itself never mentions `ownE ⊤`: it is always inside
exactly one thread's obligation.
-/

namespace AeneasIris.Semantics

open Iris BI Aeneas.Data.Coinductive
open AeneasIris.Heap (HeapGS heapInterp)
open Aeneas.Std (Result RustEffect RustHeap)

unseal Aeneas.Std.Result

section

variable {hlc : Iris.HasLC} {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]
variable [HeapGS.{0} GF] {α : Type}

/-- The postcondition thread `i` must establish.

Only the main thread's return value is observed; every other thread must never
return at all, which is `wpiAcc`'s `fun _ => False` in the spawn slot and is
what `spawn`'s trailing `endthread` discharges. -/
def threadPost (Φ : α → IProp GF) (i : Nat) : α → IProp GF :=
  if i = 0 then Φ else fun _ => iprop(False)

/-- The obligation of a thread that is **not** holding the big lock: it still
owes the mask-opening update, so it is stated at mask `⊤`. A dead thread owes
nothing. -/
def readyObl (m : Mode) (Φ : α → IProp GF) (i : Nat) : Thread α → IProp GF
  | .dead => iprop(emp)
  | .alive t => wpi_mask GF (Rust.rustH m) m t (threadPost Φ i) ⊤

/-- The obligation of the thread holding the big lock: the mask has already been
opened, so this is bare `wpi` (mask `∅`) with the closing update pushed into the
postcondition — literally the right-hand side of `wpi_mask … ⊤`. -/
def runObl (m : Mode) (Φ : α → IProp GF) (i : Nat) (t : Result α) : IProp GF :=
  wpi GF (Rust.rustH m) m t (fun v => iprop(|={∅, ⊤}=> threadPost Φ i v))

/-- `readyObl` at mask `⊤` is `runObl` behind one mask-opening update. This is
the only fact relating the two, and it is definitional. -/
theorem readyObl_alive (m : Mode) (Φ : α → IProp GF) (i : Nat) (t : Result α) :
    readyObl m Φ i (.alive t) = iprop(|={⊤, ∅}=> runObl m Φ i t) := rfl

/-- The obligation of the scheduled thread, or `emp` if there is none.

`emp` rather than `False` for the `none` case: no `Step` rule fires when the
scheduled slot is dead, so preservation is vacuous there and the weaker choice
is the more robust one. Reachable configurations always have a live `current`
anyway — `init` does, and every rule either keeps `current` alive or requires
`Config.Alive j` of its successor. -/
def focusObl (m : Mode) (Φ : α → IProp GF) (c : Config α) : IProp GF :=
  match c.focus with
  | some t => runObl m Φ c.current t
  | none => iprop(emp)

/-- **The system invariant.**

The physical heap, plus one obligation per thread. The scheduled thread's
obligation is `runObl` (mask `∅`, holding the token); every other live thread's
is `readyObl` (mask `⊤`, waiting for it). Writing the big operator over
`c.kill.threads` — the pool with the scheduled slot tombstoned — is what makes
the scheduled thread contribute `emp` there, since `readyObl _ _ _ .dead = emp`;
it avoids an index-dependent `if` and keeps the rewriting under `Step` cheap. -/
def SysInv (m : Mode) (Φ : α → IProp GF) (c : Config α) : IProp GF :=
  iprop(heapInterp c.heap ∗ focusObl m Φ c ∗
        [∗list] i ↦ th ∈ c.kill.threads, readyObl m Φ i th)

end

end AeneasIris.Semantics
