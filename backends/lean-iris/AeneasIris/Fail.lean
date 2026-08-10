import Aeneas.Std.Primitives
import AeneasIris.wpi
import AeneasIris.Rules
import Iris.Instances.Lib.Invariants

/-!
# The failure handler

`Aeneas.Std.RustEffect` covers Rust's panics *and* Aeneas' own partiality — integer
overflow, out-of-bounds indexing, division by zero. `failH` interprets all of
them as `False`.

That single choice is what makes "this code does not panic and does not
overflow" part of *every* specification rather than a separate obligation: a
weakest precondition for a tree containing a reachable `fail` is unprovable,
because at that node the handler demands `False`.

This is the `ubH` of `ub.v` in the "Program Logics à la Carte" artifact. It is a
menu item, not a law — see the note at the end of this file for the alternative.
-/

namespace AeneasIris.Fail

open Iris BI Aeneas.Data.Coinductive
open Aeneas.Std (RustEffect Error)
open AeneasIris

section Handler

variable (GF : BundledGFunctors) [Iris.InvGS_gen hlc GF]

/-- Failure is unprovable. Note `RustEffect.O` is `PEmpty`, so both continuations are
vacuous — a `fail` node has nothing after it. -/
def failH.run (_i : RustEffect.I) (_Ψ _Ψs : RustEffect.O _i → IProp GF) : IProp GF :=
  iprop(False)

def failH : Handler RustEffect GF where
  run := failH.run GF
  mono := by
    intro i Ψ Ψ' Ψs Ψs'
    simp only [failH.run]
    iintro _ _ H
    iexact H

end Handler

section Rules

variable {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]
variable {E : Effect} [RustEffect -< E] {Hd : Handler E GF} [inH (failH GF) Hd]

/-- `fail` as a program: trigger the event, then eliminate its impossible
answer. Its return type is arbitrary — the event never returns. -/
def fail {α : Type _} (e : Error) : ITree E α :=
  ITree.bind (Effect.trigger RustEffect (RustEffect.fail e)) (fun o => PEmpty.elim o)

/-- `wpi_fail`. Reaching a `fail` refutes the precondition — the goal it leaves
is `False` under a mask change, and closing it means showing the failing branch
is unreachable. There is deliberately no rule that *establishes* a weakest
precondition for `fail`: that is exactly the guarantee `failH` buys. -/
theorem wpi_fail {α : Type _} (e : Error) (Φ : Post GF α) (M : CoPset) :
    iprop(|={M, ∅}=> False) ⊢ wpi_mask GF Hd (fail (E := E) e) Φ M := by
  simp only [fail]
  refine .trans ?_ (wpi_bind (H := Hd) _ _ Φ M)
  refine .trans ?_ (wpi_trigger' (H' := failH GF) (RustEffect.fail e) _ M)
  /- The handler is `False` whatever the continuations are, so the premise is
  already in the required shape. -/
  simp only [failH, failH.run]
  exact .rfl

end Rules

/-! ## The alternative

Interpreting failure as `False` says "may not fail". Interpreting it as
`🧾 True` (`|={∅, ⊤}=> True`, the `haltH` of `halt.v`) would instead say "may
fail, but only by halting cleanly, with all invariants restored" — a genuinely
different, weaker guarantee.

Since `Error` has seven constructors, the choice can also be made *per
constructor*: `panic` is a controlled abort and could be given `haltH`'s
reading, while `undef` should stay `False`. Splitting `failH.run` on the error
is a two-line change, and nothing downstream of this file depends on which
reading is taken. That modularity is the point of the à la carte design. -/

end AeneasIris.Fail
