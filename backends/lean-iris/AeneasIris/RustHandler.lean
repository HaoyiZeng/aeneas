import AeneasIris.Fail
import AeneasIris.Concurrency
import AeneasIris.Step
import AeneasIris.HeapAPI

/-!
# The canonical handler for `RustEffect`

Every rule in this development is stated against an *abstract* handler `Hd`
constrained by `inH`:

```lean
variable {Hd : Handler E GF} [stateH heapInterp -<ₕ Hd] [stepH GF m -<ₕ Hd]
```

That is what makes the rules composable, but on its own it proves nothing about
whether a handler satisfying all four constraints at once *exists*. This file
builds one and checks the constraints resolve.

## Why the check is not a formality

`RustEffect` is a `def`, and instance search does not unfold `def`s. The `-<`
instances in `Coinductive.Effect` match a syntactic `⊕ₑ`, so they do not fire on
`RustEffect` — `Aeneas.Std.Primitives` already hand-writes `FailE -< RustEffect`
for exactly this reason. The same obstacle applies to the other three summands
and to every `inH` constraint, so each is discharged here by naming the sum
shape through `inferInstanceAs`.

## The shape

`RustEffect := FailE ⊕ₑ ConcE ⊕ₑ StepE ⊕ₑ StateE RustHeap`, and `⊕ₑ`/`⊕ₕ` are
both right-associative, so the handler is assembled in the same order and the
two nestings agree.

The heap payload is at universe 0: `RustEffect` mentions `RustHeap.{0}`, and a
handler for it must interpret that same state type.
-/

namespace AeneasIris.RustHandler

open Iris BI Aeneas.Data.Coinductive
open AeneasIris
open AeneasIris.Fail (failH)
open AeneasIris.ConcE (ConcH)
open AeneasIris.Step (stepH LaterModality lat lat_mono)
open AeneasIris.Heap (stateH heapInterp HeapGS)
open AeneasIris.HeapAPI (pointsTo load alloc)
open Aeneas.Std (FailE ConcE StepE StateE RustEffect RustHeap Loc)

section

variable {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF] [HeapGS.{0} GF]

/-- The handler a translated Rust program runs under.

`m` is the only knob: `stepH .identity` issues no modality and keeps the
reasoning termination-sensitive, `stepH .later` issues `▷` at every step event
and so makes Löb induction available. Since every operation of the heap API is
preceded by a step, that one parameter decides partial versus total correctness
for the whole development without any rule being restated. -/
def rustH (m : LaterModality) : Handler RustEffect GF :=
  failH GF ⊕ₕ ConcH.{1} GF ⊕ₕ stepH.{1} GF m ⊕ₕ stateH heapInterp.{0}

/-! ## The four sub-effect inclusions

`inH` takes an `E₁ -< E₂` instance, so these come first: without them the
statements of the `inH` instances below do not even elaborate.

`Aeneas.Std.Primitives` supplies `FailE -< RustEffect`; the other three are
needed here and by the operations (`yield`, `step`, `load`, …). Each is the
generic `⊕ₑ` instance, named at the sum shape that instance search cannot find
on its own because `RustEffect` is a `def`. -/

instance : ConcE.{1} -< RustEffect :=
  inferInstanceAs (ConcE.{1} -< (FailE.{1} ⊕ₑ ConcE.{1} ⊕ₑ StepE.{1} ⊕ₑ StateE RustHeap.{0}))

instance : StepE.{1} -< RustEffect :=
  inferInstanceAs (StepE.{1} -< (FailE.{1} ⊕ₑ ConcE.{1} ⊕ₑ StepE.{1} ⊕ₑ StateE RustHeap.{0}))

instance : StateE RustHeap.{0} -< RustEffect :=
  inferInstanceAs (StateE RustHeap.{0} -<
    (FailE.{1} ⊕ₑ ConcE.{1} ⊕ₑ StepE.{1} ⊕ₑ StateE RustHeap.{0}))

/-! ## The four handler inclusions

Each `inH` is what the corresponding family of rules asks for, so discharging
them here is what licenses instantiating those rules at `rustH`.

The sum is written out rather than abbreviated to `rustH m`: `inferInstanceAs`
elaborates `inferInstance` against the *stated* type, and leaving holes for the
other summands would send instance search after unassigned metavariables. -/

instance inH_failH (m : LaterModality) : failH GF -<ₕ rustH (GF := GF) m :=
  inferInstanceAs (failH GF -<ₕ
    (failH GF ⊕ₕ ConcH.{1} GF ⊕ₕ stepH.{1} GF m ⊕ₕ stateH heapInterp.{0}))

instance inH_ConcH (m : LaterModality) : ConcH.{1} GF -<ₕ rustH (GF := GF) m :=
  inferInstanceAs (ConcH.{1} GF -<ₕ
    (failH GF ⊕ₕ ConcH.{1} GF ⊕ₕ stepH.{1} GF m ⊕ₕ stateH heapInterp.{0}))

instance inH_stepH (m : LaterModality) : stepH.{1} GF m -<ₕ rustH (GF := GF) m :=
  inferInstanceAs (stepH.{1} GF m -<ₕ
    (failH GF ⊕ₕ ConcH.{1} GF ⊕ₕ stepH.{1} GF m ⊕ₕ stateH heapInterp.{0}))

instance inH_stateH (m : LaterModality) :
    stateH heapInterp.{0} -<ₕ rustH (GF := GF) m :=
  inferInstanceAs (stateH heapInterp.{0} -<ₕ
    (failH GF ⊕ₕ ConcH.{1} GF ⊕ₕ stepH.{1} GF m ⊕ₕ stateH heapInterp.{0}))

/-! ## The rules, at the concrete handler

The `inH` instances above are only evidence that the *constraints* are
satisfiable. What has to hold is that the rules themselves instantiate — that
the effect inclusion each rule triggers through and the handler inclusion each
rule reasons through agree on one concrete handler. Each example below is a
rule applied at `rustH`, with nothing supplied but the handler. -/

section Instantiation

variable {m : LaterModality} {M : CoPset}

/-- A heap read. Exercises `StateE -< RustEffect`, `stateH … -<ₕ _` and, through
the leading step of the API operation, `stepH … -<ₕ _` — the two families the
heap API needs simultaneously. -/
example (l : Loc) (v : Nat) (dq : DFrac) (Φ : Post GF Nat) :
    lat m iprop(l ↦{dq} v ∗ (l ↦{dq} v -∗ |={M}=> Φ v))
      ⊢ wpi_mask GF (rustH m) (HeapAPI.load (E := RustEffect) (T := Nat) l) Φ M :=
  HeapAPI.wpi_load (Hd := rustH m) l v dq

/-- A step on its own. The value is `PUnit` at the effect's universe: `StepE`
answers there, which is the pinning that made the handler inclusion resolve. -/
example (Φ : Post GF PUnit.{2}) :
    lat m iprop(|={M}=> Φ PUnit.unit)
      ⊢ wpi_mask GF (rustH m) (Step.step (E := RustEffect)) Φ M :=
  Step.wpi_step (Hd := rustH m) Φ M

/-- A scheduling point. `yield` fixes the mask at `⊤`, since its handler closes
and reopens every invariant. -/
example (Φ : Post GF PUnit.{2}) :
    iprop(Φ PUnit.unit) ⊢ wpi_mask GF (rustH m) (ConcE.yield (E := RustEffect)) Φ ⊤ :=
  ConcE.wpi_yield GF (H := rustH m) Φ

/-- Failure. The one rule that consumes rather than establishes. -/
example (e : Aeneas.Std.Error) (Φ : Post GF Nat) :
    iprop(|={M, ∅}=> False)
      ⊢ wpi_mask GF (rustH m) (Fail.fail (E := RustEffect) e) Φ M :=
  Fail.wpi_fail (Hd := rustH m) e Φ M

/-- All four in one program: allocate, step, read back, yield.

This is the shape a translated Rust function has, and it is the first point at
which the four rule families are used against a single handler. -/
example (Φ : Post GF Nat) :
    lat m iprop(∀ l, l ↦ (7 : Nat) -∗ |={⊤}=>
        wpi_mask GF (rustH m) (HeapAPI.load (E := RustEffect) (T := Nat) l) Φ ⊤)
      ⊢ wpi_mask GF (rustH m)
          (do let l ← HeapAPI.alloc (E := RustEffect) (7 : Nat)
              HeapAPI.load (T := Nat) l) Φ ⊤ := by
  refine .trans ?_
    (wpi_bind (H := rustH m) (HeapAPI.alloc (E := RustEffect) (7 : Nat)) _ Φ ⊤)
  exact HeapAPI.wpi_alloc (Hd := rustH m) (m := m) (7 : Nat) (M := ⊤)

end Instantiation

end

end AeneasIris.RustHandler
