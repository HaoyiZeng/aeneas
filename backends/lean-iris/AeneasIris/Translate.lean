import Aeneas.Data.Coinductive.ITree
import Aeneas.Data.Coinductive.Effect

/-!
# Re-indexing a tree along a sub-effect inclusion

`ITree.translate` is a standard combinator of the ITree library — the Coq
development uses it exactly this way, and states `wpi_inH_emp_mask` in terms of
it. The Lean port is minimal (`bind`, `iter`, `trigger`), so it is supplied
here rather than upstream: keeping it downstream means the Aeneas backend needs
no change at all for a client to add its own effects.

Why it is needed: `Aeneas.Std.Result` fixes the effect signature to
`RustEffect`. The ITree design offers two ways to compose — write programs
polymorphically in `E` (`{E} [FailE -< E]`), or keep them closed and translate.
Fixing `Result` forecloses the first, so the second is the route.
-/

namespace AeneasIris

open Aeneas.Data.Coinductive

/-- Re-index a tree along a sub-effect inclusion: every event is replaced by its
image in the larger signature, and the answer is mapped back.

This is what lets a translated Rust program — which lives in `ITree RustEffect`
— be sequenced inside a computation over a larger signature, such as one that
also carries a heap. It is defined by `partial_fixpoint` like `bind`, so no
`tau` constructor is needed to make it productive: a degenerate case falls to
`div` rather than being rejected. -/
def ITree.translate {E₁ : Effect.{u}} {E₂ : Effect.{v}} [E₁ -< E₂] {R : Type w}
    (t : ITree.{w, u} E₁ R) : ITree.{w, v} E₂ R :=
  match t.unfold with
  | .ret r => .ret r
  | .div => .div
  | .vis i k =>
    let ⟨i₂, f⟩ := Subeffect.map (E₁ := E₁) i
    .vis i₂ (fun o => ITree.translate (k (f o)))
partial_fixpoint

@[simp]
theorem itree_ret_translate {E₁ : Effect.{u}} {E₂ : Effect.{v}} [E₁ -< E₂] {R : Type w}
    (r : R) : ITree.translate (E₁ := E₁) (E₂ := E₂) (.ret r) = .ret r := by
  rw [ITree.translate]
  simp [ITree.ret, ITree.fold, ITree.unfold]

@[simp]
theorem itree_div_translate {E₁ : Effect.{u}} {E₂ : Effect.{v}} [E₁ -< E₂] {R : Type w} :
    ITree.translate (E₁ := E₁) (E₂ := E₂) (R := R) .div = .div := by
  rw [ITree.translate]
  simp [ITree.div, ITree.fold, ITree.unfold]

@[simp]
theorem itree_vis_translate {E₁ : Effect.{u}} {E₂ : Effect.{v}} [E₁ -< E₂] {R : Type w}
    (i : E₁.I) (k : E₁.O i → ITree E₁ R) :
    ITree.translate (E₂ := E₂) (.vis i k)
      = .vis (Subeffect.map (E₁ := E₁) i).1
          (fun o => ITree.translate (k ((Subeffect.map (E₁ := E₁) i).2 o))) := by
  rw [ITree.translate]
  simp [ITree.vis, ITree.fold, ITree.unfold]


/-- `pure` is `ret`, but the two are not syntactically equal, so the `ret`
equation does not fire on goals phrased with `do`-notation. -/
@[simp]
theorem itree_pure_translate {E₁ : Effect.{u}} {E₂ : Effect.{v}} [E₁ -< E₂] {R : Type w}
    (r : R) : ITree.translate (E₁ := E₁) (E₂ := E₂) (pure r) = pure r :=
  itree_ret_translate r

/-- `translate` is a monad morphism.

This is the property that makes the combinator usable at all: without it a
translated program could not be taken apart along its binds, and every rule
about sequencing would have to be restated for translated trees. -/
theorem translate_bind {E₁ : Effect.{u}} {E₂ : Effect.{v}} [E₁ -< E₂] {α : Type w} {β : Type w}
    (t : ITree.{w, u} E₁ α) (f : α → ITree.{w, u} E₁ β) :
    ITree.translate (E₂ := E₂) (t >>= f)
      = ITree.translate t >>= (fun a => ITree.translate (f a)) := by
  ext n
  induction n generalizing t
  · congr 0
  · cases t <;> simp [*]

end AeneasIris
