import Iris.ProofMode
import Iris.BI.Lib.Fixpoint
import Aeneas.Std.Delab

/-!
# Atomic updates with packed binders

An atomic update quantifies over however many variables the caller writes:

    AU ⟪ ∃∃ s v, isRwLock γ l s v ⟫ @ ⊤, ∅ ⟪ ∀∀ r, β s v r, COMM Φ r ⟫

Coq's Iris reifies that binder sequence as a *telescope*, and the Lean port
follows. The cost is that goals fill with `Tele.app`/`ULift.up`/`Sigma`/`PUnit`,
which a bespoke tactic (`itele_reduce`) then has to scrub before `icases` can
name the binders.

Here the binders are packed into an ordinary right-nested product by the macro,
which is what Aeneas already does for `⦃ ⦄` postconditions and `do` notation
(`Aeneas/Std/WP.lean`, `Aeneas/Do/Delab.lean`). Two pieces make that invisible:

* an `IntoExists` instance, so `icases` peels the packing *natively* -- one
  instance covers every arity, because peeling one binder leaves a value of the
  same shape;
* a delaborator, so an update prints back as the notation that produced it
  rather than as its packing.

Neither needs a reduction tactic: `Prod` is native, so there is nothing custom
left in the goal to reduce away.
-/

namespace AeneasIris.AtomicP

open Iris Iris.BI Iris.ProofMode
open Lean PrettyPrinter Delaborator SubExpr

/-! ## Packing

`auUncurry` is `Aeneas.Std.uncurry` specialised to a `PROP`-valued family. It is
a separate definition for two reasons: the `IntoExists` instance below needs a
stable head symbol to match on, and the delaborator distinguishes it from
`Std.uncurry` (which prints as a *tuple* binder `(a, b) => …`) to print
*separate* binders `a b => …`. Compare `Aeneas.Std.WP.uncurry'`, which exists for
exactly the same reason. -/
def auUncurry {α β : Type} {PROP : Type _} (p : α → β → PROP) : α × β → PROP :=
  fun (x, y) => p x y

@[simp] theorem auUncurry_pair {α β : Type} {PROP : Type _}
    (x : α) (y : β) (p : α → β → PROP) : auUncurry p (x, y) = p x y := rfl

theorem auUncurry_eq {α β : Type} {PROP : Type _}
    (x : α × β) (p : α → β → PROP) : auUncurry p x = p x.fst x.snd := rfl

section
variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]

/-! ## Peeling

The instance that makes the packing invisible to `icases`.

One instance suffices for every arity. Packing is right-nested, so peeling the
outermost component leaves an existential over `R` -- and when `R` is itself a
product, this instance applies again. The chain bottoms out at a non-product
existential, which `intoExists_exists` already handles.

It matches on the *existential*, not on the family: in `atomicAcc` the body is
`α x ∗ (abort ∧ commit)`, so an instance keyed on `auUncurry Ψ p` never fires.

It must outrank `intoExists_exists`, which matches any existential and would
otherwise hand back the packed pair.

It is `scoped` because it changes how *every* product existential destructs.
That is what we want inside atomic proofs and nowhere else, so it is opt-in
via `open AeneasIris.AtomicP`. -/
scoped instance (priority := high) intoExistsProd {A R : Type} (Φ : A × R → PROP) :
    IntoExists (iprop(∃ p : A × R, Φ p)) (fun a : A => iprop(∃ r : R, Φ (a, r))) where
  into_exists := by
    iintro ⟨%p, H⟩
    iexists p.1, p.2
    iexact H

/-! ## The update

Shape-for-shape the usual definition; only the binder representation differs, so
the monotonicity the fixpoint needs is still proved once, generically. -/

/-- One atomic accessor: open the world from `Eo` to `Ei`, hand over `α x`, and
offer the choice of putting it back (`P`) or committing (`β x y`). -/
def atomicAcc {A B : Type} (Eo Ei : CoPset)
    (α : A → PROP) (P : PROP) (β Φ : A → B → PROP) : PROP :=
  iprop(|={Eo,Ei}=> ∃ x, α x ∗ ((α x ={Ei,Eo}=∗ P) ∧ (∀ y, β x y ={Ei,Eo}=∗ Φ x y)))

/-- Monotonicity of the accessor in its abort slot.

This is what the greatest fixpoint requires, and the reason the shape is kept
fixed: it is proved **once**, generically in `α`, `β`, `Φ` and in the arity --
which is packed away inside `A` and `B` and never mentioned. Compare the
telescoped development, which proves the same thing once for the same reason
(`Iris/BI/Lib/Atomic.lean:105`). -/
instance atomicAccMono {A B : Type} (Eo Ei : CoPset)
    (α : A → PROP) (β Φ : A → B → PROP) :
    BIMonoPred (PROP := PROP) (A := Unit)
      (fun Ψ (_ : Unit) => atomicAcc Eo Ei α (Ψ ()) β Φ) where
  mono_pred := by
    intro Ψ Ψ' _ _
    iintro #Hmono %u H
    simp only [atomicAcc] at *
    imod H with ⟨%x, Hα, Hclose⟩
    imodintro
    iexists x
    isplitl [Hα]
    · iexact Hα
    · isplit
      · iintro Hα'
        icases Hclose with ⟨Habort, -⟩
        imod Habort $$ Hα' with HP
        imodintro
        iapply Hmono $$ HP
      · iapply and_elim_r $$ Hclose
  mono_pred_ne := by infer_instance

/-- The atomic update: the accessor whose abort branch hands back the update
itself, so it survives a failed attempt and can be retried. -/
def atomicUpdate {A B : Type} (Eo Ei : CoPset)
    (α : A → PROP) (β Φ : A → B → PROP) : PROP :=
  bi_greatest_fixpoint (fun Ψ (_ : Unit) => atomicAcc Eo Ei α (Ψ ()) β Φ) ()

/-- Unfolding: an update is its own accessor with itself in the abort slot.

Everything a proof needs follows from this: `imod` on the `fupd`, then `icases`
peels the binders (natively, via `intoExistsAuUncurry`), and the two branches of
the `∧` are abort and commit. -/
theorem aupd_unfold {A B : Type} (Eo Ei : CoPset)
    (α : A → PROP) (β Φ : A → B → PROP) :
    atomicUpdate Eo Ei α β Φ ⊢ atomicAcc Eo Ei α (atomicUpdate Eo Ei α β Φ) β Φ := by
  conv => lhs; unfold atomicUpdate
  exact greatest_fixpoint_unfold_mp
    (F := fun Ψ (_ : Unit) => atomicAcc Eo Ei α (Ψ ()) β Φ) (x := ())

/-! ## Notation

`AU ⟪ ∃ x y z, α ⟫ @ Eo, Ei ⟪ ∀ u v, β, COMM Φ ⟫`, with any number of binders
on either side.

The macro folds the binder list into a right-nested product exactly as Aeneas'
`⦃ ⦄` postcondition macro does (`Aeneas/Std/WP.lean`, `buildUncurryLam`): one
binder needs no packing at all, and each further binder adds one `auUncurry`
layer. Since `auUncurry` is what `intoExistsAuUncurry` matches on, every arity
peels natively when the update is opened. -/

section Notation
open Lean

/-- Fold binders into a packed family: `[x, y, z]` ↦ `auUncurry fun x => auUncurry fun y z => …`.

A single binder is left curried, so the common case introduces no packing. -/
partial def buildAuLam (xs : List Ident) (body : Term) : MacroM Term := do
  let u := mkIdent ``auUncurry
  match xs with
  | []        => `(fun _ => $body)
  | [x]       => `(fun $x => $body)
  | [a, b]    => `($u (fun $a $b => $body))
  | a :: rest => do `($u (fun $a => $(← buildAuLam rest body)))

declare_syntax_cat auPre
declare_syntax_cat auPost
syntax "⟪ " ("∃ " ident+ ", ")? term " ⟫" : auPre
syntax "⟪ " ("∀ " ident+ ", ")? term ", " "COMM " term " ⟫" : auPost

syntax:max "AU " ppRealFill(auPre ppSpace "@ " term ", " term ppSpace auPost) : term

macro_rules
  | `(AU ⟪ $[∃ $xs* , ]? $α:term ⟫ @ $Eo:term, $Ei:term
         ⟪ $[∀ $ys* , ]? $β:term, COMM $Φ:term ⟫) => do
      let xs : List Ident := (xs.map (·.toList)).getD []
      let ys : List Ident := (ys.map (·.toList)).getD []
      let mkOuter (inner : Term) : MacroM Term := buildAuLam xs inner
      let mkInner (b : Term) : MacroM Term := do buildAuLam xs (← buildAuLam ys b)
      `(atomicUpdate $Eo $Ei
          $(← mkOuter (← `(iprop($α))))
          $(← mkInner (← `(iprop($β))))
          $(← mkInner (← `(iprop($Φ)))))

end Notation

/-! ## Display

Without this an opened update shows its *representation* --

    atomicUpdate Eo Ei (auUncurry fun a => auUncurry fun b c => α a b c) …

-- which is exactly the leak the packing was supposed to hide. The delaborator
prints it back as the notation that produced it. This is the same move, for the
same reason, as `Aeneas.Std.WP.delabSpec`; the chain-walking helpers are reused
verbatim from `Aeneas.Std.Delab`.

The three families share their binder *names*, because `buildAuLam` builds all
three from the same identifiers -- so each can be peeled independently and the
names still agree. -/

section Delab
open Lean PrettyPrinter Delaborator SubExpr Aeneas.Std.Delab

/-- Walk a packed family, flattening `auUncurry` layers into a flat binder list.

The `auUncurry` analogue of `enterUncurryChain`; the difference is only which
head symbol is chased, and it matters: `Std.uncurry` prints as a *tuple* binder,
`auUncurry` as separate binders. -/
private partial def enterAuChain (acc : Array BinderEntry)
    (k : Array BinderEntry → DelabM α) : DelabM α := do
  match (← getExpr) with
  | .lam n _ b _ =>
    if b.hasLooseBVars then
      let pos ← getPos
      withBindingBody' n pure fun fv => enterAuChain (acc.push (fv.fvarId!, n, pos)) k
    else
      /- A binder the body never mentions: this is how `buildAuLam` encodes
         *no* binders (`fun _ => body`), which is the common case on the commit
         side. Enter it, but do not report it, so the round trip is exact.
         Recurse rather than stop: with no binders on *either* side the encoding
         is two nested vacuous lambdas. -/
      withBindingBody' n pure fun _ => enterAuChain acc k
  | e =>
    if e.isAppOfArity ``auUncurry 4 then withAppArg <| enterAuChain acc k
    else k acc

/-- Peel a packed family into `(binders, body)`. -/
private def delabAuFamily : DelabM (Array Term × Term) :=
  enterAuChain #[] fun entries => delabBinders entries.toList delab

/-- The notation takes identifiers, so anything `delabBinders` turned into a
pattern (a tuple, a constructor) cannot be printed this way; give up and let the
default delaborator show the raw term rather than print something misleading. -/
private def toIdents (ts : Array Term) : DelabM (Array Ident) :=
  ts.mapM fun t => if t.raw.isIdent then pure ⟨t.raw⟩ else failure

/-- `atomicUpdate Eo Ei α β Φ` → `AU ⟪ ∃ x.., α ⟫ @ Eo, Ei ⟪ ∀ y.., β, COMM Φ ⟫`.

`β` and `Φ` carry the pre-binders *and* the post-binders in one chain, and
nothing in the packing says where the split is -- so the pre-arity is read off
`α`, whose chain is exactly the pre-binders, and the rest of `β`'s chain is the
post-binders. -/
@[scoped delab app.AeneasIris.AtomicP.atomicUpdate]
def delabAtomicUpdate : Delab := do
  guard <| (← getExpr).isAppOfArity ``atomicUpdate 10
  let Eo ← withNaryArg 5 delab
  let Ei ← withNaryArg 6 delab
  let (preT,  aBody) ← withNaryArg 7 delabAuFamily
  let (allT,  bBody) ← withNaryArg 8 delabAuFamily
  let (_,     fBody) ← withNaryArg 9 delabAuFamily
  let pre  ← toIdents preT
  let post ← toIdents (allT.extract preT.size allT.size)
  let preStx  ← if pre.isEmpty  then `(auPre| ⟪ $aBody ⟫)
                                else `(auPre| ⟪ ∃ $pre*, $aBody ⟫)
  let postStx ← if post.isEmpty then `(auPost| ⟪ $bBody, COMM $fBody ⟫)
                                else `(auPost| ⟪ ∀ $post*, $bBody, COMM $fBody ⟫)
  `(AU $preStx:auPre @ $Eo, $Ei $postStx:auPost)

end Delab

/-! ## Round-trip tests

Each of these prints back exactly the notation that produced it. They are the
regression tests for the packing: if a change makes the representation leak,
one of these fails with the raw `auUncurry` term. -/

section Tests
variable {A B : Type} (α : A → PROP) (β Φ : A → B → PROP)
variable (α3 : A → A → A → PROP) (β3 Φ3 : A → A → A → B → PROP)
variable (α0 β0 Φ0 : PROP) (Eo Ei : CoPset)

/-- info: AU ⟪ ∃ x, α x ⟫ @ Eo, Ei ⟪ ∀ y, β x y, COMM Φ x y ⟫ : PROP -/
#guard_msgs in
#check (AU ⟪ ∃ x, α x ⟫ @ Eo, Ei ⟪ ∀ y, β x y, COMM Φ x y ⟫)

/-- info: AU ⟪ ∃ a b c, α3 a b c ⟫ @ Eo, Ei ⟪ ∀ d, β3 a b c d, COMM Φ3 a b c d ⟫ : PROP -/
#guard_msgs in
#check (AU ⟪ ∃ a b c, α3 a b c ⟫ @ Eo, Ei ⟪ ∀ d, β3 a b c d, COMM Φ3 a b c d ⟫)

/-- info: AU ⟪ α0 ⟫ @ Eo, Ei ⟪ β0, COMM Φ0 ⟫ : PROP -/
#guard_msgs in
#check (AU ⟪ α0 ⟫ @ Eo, Ei ⟪ β0, COMM Φ0 ⟫)

end Tests

end

end AeneasIris.AtomicP
