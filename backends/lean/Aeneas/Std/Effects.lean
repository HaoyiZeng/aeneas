import Std.Data.ExtTreeMap
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

/-! ## The heap

The state a translated Rust program threads. Only the *type* is here: the
operations, the handler and the reasoning rules need Iris and live in
`AeneasIris.Heap`. `RustEffect` mentions this type, which is why it cannot stay
on the Iris side.

Aeneas is a shallow embedding — a Rust type becomes a real Lean type — so a
shared cell holds a value of an arbitrary Lean type and different cells hold
different ones. `Val` therefore pairs a type with an inhabitant of it. That
pairing is the sole reason the heap sits one universe above its payload:
function types take `max`, only packing a type as data adds one.

Consequently a value whose type mentions `Result` can never be stored, at any
universe: `Result` is one level above the payload, and raising the payload
raises `Result` with it. Rust *data* types do not mention `Result` and are
storable; closures and trait dictionaries are not. -/

/-- Locations. -/
abbrev Loc := Nat

/-- Whether a cell is being written, or read by `n` readers.

The states and transitions are λRust's (`lambda-rust/lang/lang.v`), where a
data race is a configuration in which no rule applies — the program is stuck,
and a weakest precondition implies progress. -/
inductive AccessState where
  | writing
  | reading (n : Nat)
deriving DecidableEq

/-- A cell: its concurrency state and its value. -/
abbrev Cell (V : Type u) : Type u := AccessState × V

/-- A dynamically typed value: a type together with an inhabitant of it. -/
def Val : Type (u + 1) := (T : Type u) × T

/-- Pack a value, remembering its type. -/
abbrev Val.pack {T : Type u} (x : T) : Val.{u} := ⟨T, x⟩

/-- Read a packed value back at an expected type, or `default` if it was stored
at a different one.

`noncomputable` because equality of types is not decidable. That is not a
restriction in practice: only hand-written models touch the heap, and the rules
in the program logic never reach the `default` branch — a points-to assertion
fixes the type of the cell, so the projection at that type always succeeds. -/
noncomputable def Val.unpack (T : Type u) [Inhabited T] (v : Val.{u}) : T :=
  open Classical in
  if h : v.1 = T then h ▸ v.2 else default

/-- Packing and reading back at the same type is the identity. This is the whole
point of storing the type alongside the value. -/
@[simp] theorem Val.unpack_pack (T : Type u) [Inhabited T] (x : T) :
    Val.unpack T (Val.pack x) = x := by
  simp [Val.unpack]

/-- Reading back at a *different* type recovers nothing. Stated so that the
absence of a `Val.unpack (Val.pack x) = x` for mismatched types is visible
rather than merely unprovable. -/
theorem Val.unpack_pack_ne {T U : Type u} [Inhabited U] (x : T) (h : T ≠ U) :
    Val.unpack U (Val.pack x) = default := by
  simp [Val.unpack, h]

/-- Needed so that a read from an absent location has something to return. -/
instance : Inhabited Val.{u} := ⟨Val.pack PUnit.unit⟩

/-- Comparing two `Val`s means comparing their *types* first, and equality of
types is not decidable. The instance is therefore classical, and `noncomputable`
like `Val.unpack`.

The semantics are the intended ones: `⟨T, x⟩ = ⟨U, y⟩` holds exactly when the
types agree and the values do. A compare-and-swap against a cell holding a
different type fails, which is what it should do. -/
noncomputable instance : DecidableEq Val.{u} :=
  fun a b => Classical.propDecidable (a = b)

/-- The heap.

`Std.ExtTreeMap` is Lean's own, so naming it here costs no new dependency; the
`LawfulFiniteMap` instance the reasoning needs is supplied on the Iris side
(`Iris/Std/HeapInstances.lean`). -/
abbrev HMap (V : Type u) : Type u := Std.ExtTreeMap Loc V compare

abbrev RustHeap : Type (u + 1) := HMap (Cell Val.{u})

end Aeneas.Std
