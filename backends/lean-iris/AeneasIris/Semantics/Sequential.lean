import AeneasIris.Rust

/-!
# `Sequential`: handlers that ignore the thread-spawning continuation

The paper's `threadpool_adequacy` (`src/threadpool/interleaving.v`) and its
`state_adequacy` / `step_adequacy` (`src/state.v`, `src/step.v`) all carry a side
condition the Lean port never stated:

```coq
Class Sequential {Σ E} (H : iHandler Σ E) :=
  is_seq : ∀ A e Φ s, H A e Φ s -∗ H A e Φ (const False).
```
(`src/handler.v:99`)

It says a handler makes no use of its second continuation — the one `wpiAcc`
feeds forked threads. In the artifact it is what lets the sequential effects be
interpreted away *after* concurrency has been scheduled into a single tree.

**We never need it**, because the direct machine of `Semantics/Machine.lean`
does not decompose the effect row: `Step` handles all four summands at once, so
there is no residual handler to constrain. But an independent review pointed out
that the condition was not merely unused — it was *accidentally satisfied* and
nowhere recorded, which is a fragile state for a hypothesis to be in. So it is
stated and discharged here.

`ConcH` is, of course, **not** sequential: `ConcH.run .fork Ψ Ψs = Ψ .cur ∗ Ψs .new`
is precisely the clause that uses the spawn continuation. That is why the
instance below is for `rustH`'s *other three* summands. (Proving
`¬ Sequential ConcH` would need a consistency argument for the ambient logic —
`Ψ .cur ∗ Ψs .new ⊢ Ψ .cur ∗ False` forces `emp ⊢ False` at `Ψ = Ψs = fun _ => emp` —
which is beside the point here.)
-/

namespace AeneasIris.Semantics

open Iris BI Aeneas.Data.Coinductive
open AeneasIris
open AeneasIris.Fail (failH)
open AeneasIris.Step (stepH)
open AeneasIris.Heap (stateH heapInterp StateInterp HeapGS)
open Aeneas.Std (RustHeap)

/-- A handler that ignores the thread-spawning continuation.

The artifact's `Sequential` (`src/handler.v`), transliterated. Every summand of
`rustH` except `ConcH` satisfies it, and each does so *definitionally* — the
clauses simply bind the second continuation and never mention it again. -/
class Sequential {GF : BundledGFunctors} {E : Effect} (H : Handler E GF) : Prop where
  is_seq : ∀ (i : E.I) (Ψ B : E.O i → IProp GF),
    H.run i Ψ B ⊢ H.run i Ψ (fun _ => iprop(False))

section

variable {hlc : Iris.HasLC} {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]

/-- Failure is unprovable whatever the continuations are. -/
instance failH_sequential : Sequential (failH GF) where
  is_seq _ _ _ := .rfl

/-- `stepH` applies the chosen modality to the main continuation only. -/
instance stepH_sequential (m : Mode) : Sequential (stepH.{u} GF m) where
  is_seq i _ _ := by cases i; exact .rfl

/-- The state handler threads the state interpretation through the main
continuation only. -/
instance stateH_sequential {S : Type u} (SI : StateInterp S GF) :
    Sequential (stateH SI) where
  is_seq i _ _ := by cases i; exact .rfl

/-- Sequentiality is closed under `⊕ₕ`, by cases on which summand fires. -/
instance sum_sequential {E₁ E₂ : Effect} (H₁ : Handler E₁ GF) (H₂ : Handler E₂ GF)
    [S₁ : Sequential H₁] [S₂ : Sequential H₂] : Sequential (H₁ ⊕ₕ H₂) where
  is_seq i Ψ B :=
    match i with
    | .inl i₁ => S₁.is_seq i₁ Ψ B
    | .inr i₂ => S₂.is_seq i₂ Ψ B

variable [HeapGS.{0} GF]

/-- **A sequential residual handler.**

This is the hypothesis the artifact's adequacy chain would need of the residual
handler once `ConcE` has been scheduled away.

**Read the statement carefully.** The handler below is *hand-assembled*:
`failH ⊕ₕ stepH ⊕ₕ stateH`, at effect `FailE ⊕ₑ StepE ⊕ₑ StateE`. It is **not**
a subterm of `rustH = failH ⊕ₕ (ConcH ⊕ₕ (stepH ⊕ₕ stateH))`, and nothing in
this development derives it from `rustH` by an actual operation — deleting a
summand from the middle of a nested `⊕ₕ` is not something the `Handler` algebra
here provides. So this instance records that the three *non-concurrent*
components of `rustH` are individually and jointly sequential, which is the
substance of the condition; it does not mechanically connect that fact to
`rustH` itself. -/
instance rustSeq_sequential (m : Mode) :
    Sequential (failH GF ⊕ₕ stepH.{1} GF m ⊕ₕ stateH heapInterp.{0}) :=
  inferInstance

end

end AeneasIris.Semantics
