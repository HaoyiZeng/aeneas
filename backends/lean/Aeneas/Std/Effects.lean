import Aeneas.Data.Coinductive.ITree
import Aeneas.Data.Coinductive.Effect

/-!
# Effect signatures

The operations a translated Rust program may perform. A signature is a set of
operation names together with the type each returns; it says nothing about what
the operations *mean*. Meaning is supplied by a handler, and handlers are
separation-logic predicates, so they live in the `aeneas-iris` package. Keeping
the signatures here is what lets `RustEffect` mention them without `aeneas`
depending on Iris.

These were previously on the Iris side, so that a client could assemble its own
signature with `RustEffect` as one summand. That does not work for stateful
reasoning: generated code lives in `Result = ITree RustEffect`, so an effect
that is not a summand of `RustEffect` can never appear in a generated program,
and there is nothing for the program logic to reason about. The signatures
therefore have to be visible to `RustEffect` itself.

Everything here is universe-polymorphic. The payload universe of the heap is a
parameter (see `StateE`), and `SumE` requires all summands to share one
universe, so the small effects must follow it up. No `ULift` is needed: their
constructors take at most `Error : Type 0`, and an inductive may be declared at
any universe at least as large as its constructors' arguments.
-/

namespace Aeneas.Std

open Aeneas.Data.Coinductive

universe u

/-! ## Failure

`Error` lives here rather than in `Primitives` because `FailE` mentions it and
`RustEffect` is assembled from the signatures below. Its full name is unchanged.
-/

inductive Error where
   | assertionFailure: Error
   | integerOverflow: Error
   | divisionByZero: Error
   | arrayOutOfBounds: Error
   | maximumSizeExceeded: Error
   | panic: Error
   | undef: Error
deriving Repr, BEq

/-! ### The failure effect

Rust's panics and Aeneas' own partiality (integer overflow, out-of-bounds
indexing, …). The answer type is empty: the operation never returns, so a `fail`
node has no continuation. -/

inductive FailE.I : Type u where
  | fail : Error → FailE.I

def FailE.O : FailE.I.{u} → Type u
  | .fail _ => PEmpty

def FailE : Effect.{u} := ⟨FailE.I, FailE.O⟩

/-! ## Concurrency

First-order, in the style of the "Program Logics à la Carte" development: the
body of a spawned thread is the *continuation*, Unix-fork style, which is why
`fork` returns a two-element tag rather than taking a thread as an argument.

`yield` is the only place control may pass to another thread, so the distance
between two yields is exactly what "atomic" means here. `endthread` never
returns. -/

inductive ConcE.Tags : Type u where
  | cur
  | new

inductive ConcE.I : Type u where
  | fork : ConcE.I
  | yield : ConcE.I
  | endthread : ConcE.I

def ConcE.O : ConcE.I.{u} → Type u
  | .fork => ConcE.Tags
  | .yield => PUnit
  | .endthread => PEmpty

def ConcE : Effect.{u} := ⟨ConcE.I, ConcE.O⟩

/-! ## Steps

A marker with no computational content. `wpi` is a least fixpoint and so is
termination-sensitive by default; a handler may answer a `step` under `▷`, which
makes Löb induction available and hence buys termination-*insensitive*
reasoning. Whether a `▷` is actually issued is the handler's choice, not a
property of the weakest precondition. -/

inductive StepE.I : Type u where
  | step

def StepE.O : StepE.I.{u} → Type u
  | .step => PUnit

def StepE : Effect.{u} := ⟨StepE.I, StepE.O⟩

/-! ## State

A single primitive: transform the state, or get stuck. Every read-modify-write
is therefore *one* event, so there is no window in which the state could change
between reading it and updating it — which is what lets the handler be stated
without the "half the authoritative element inside an invariant" construction
the paper needs for its two-event `get`/`set` presentation.

`none` is how undefined behaviour is expressed: the handler demands
`⌜f s = some s'⌝`, which is unprovable when the transformation is undefined at
`s`, so no execution can take the step. -/

section
variable (S : Type u)

inductive StateE.I : Type u where
  | modify (f : S → Option S)

def StateE.O : StateE.I S → Type u
  | .modify _ => S

def StateE : Effect.{u} := ⟨StateE.I S, StateE.O S⟩
end

end Aeneas.Std
