import AeneasIris.AtomicP
import AeneasIris.wpi

/-!
# Logically atomic triples for `wpi`

The triple that goes with `AtomicP.atomicUpdate`: the client is handed an atomic
update, and must produce a `wpi`.

This is `Iris/ProgramLogic/Atomic.lean` with the telescopes removed. The removal
is not cosmetic there either -- the reference spells out `Tele.cons`, `Tele.app`
and `ULift.up` by hand in *every* macro rule, so a new arity means a new rule,
and the rules are not interchangeable. Packing puts the arity inside the type,
so the definition and the notation are each written once.

`auUncurry` is what makes this work for `f` and `POST` as well as for the
predicates: its codomain is an unconstrained `Type _`, so the same packing that
folds `α : A → PROP` folds `f : A → B → P → V` and
`POST : A → B → P → Option PROP`.
-/

namespace AeneasIris.AtomicWpi

open Iris BI Aeneas.Data.Coinductive AeneasIris AeneasIris.AtomicP

section

variable {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]

/-- `P -∗? Q` is `Q` when there is no `P`.

The postcondition of a triple is optional, and threading `True -∗ Q` through
every spec that does not use one is noise. Same definition and same purpose as
`Iris.wandM`; it is repeated here so this file does not depend on the telescoped
development. -/
def wandM (P : Option (IProp GF)) (Q : IProp GF) : IProp GF :=
  match P with
  | some P => iprop(P -∗ Q)
  | none   => Q

@[simp] theorem wandM_none (Q : IProp GF) : wandM none Q = Q := rfl
@[simp] theorem wandM_some (P Q : IProp GF) : wandM (some P) Q = iprop(P -∗ Q) := rfl

/-- A logically atomic triple.

`E` is the mask the *implementation* reserves; the client's update runs at
`⊤ \ E`, so a client cannot open what the implementation is using.

The two postconditions differ in when they are owed. `β` is the new state of the
shared resource and is handed over *at* the linearisation point, so it must be
committed atomically. `POST` is the caller's private receipt -- a guard, a
handle, a borrow -- which nobody else can observe, so forcing it through the
linearisation point would only make the spec harder to use. `f` is the value the
tree returns. -/
def atomicWpi {Eff : Effect.{u}} {V : Type v} {A B P : Type}
    (Hd : Handler Eff GF) (t : ITree Eff V) (E : CoPset)
    (α : A → IProp GF) (β : A → B → IProp GF)
    (POST : A → B → P → Option (IProp GF)) (f : A → B → P → V) : IProp GF :=
  iprop(∀ Φ : Post GF V,
    atomicUpdate (⊤ \ E) ∅ α β (fun x y => iprop(∀ z, wandM (POST x y z) (Φ (f x y z)))) -∗
    wpi_mask GF Hd t Φ ⊤)

/-! ## Notation

`AWP ⟪ ∀ x.., α ⟫ Hd t @ E ⟪ ∃ y.., β | z.., RET v; POST ⟫`, with any number of
binders in each of the three groups, and `RET`-binders and `POST` both optional.

**One rule covers every combination.** The reference needs a separate rule per
shape because each spells out its own telescope scaffolding; here the arity is
inside the packed type, so the shape is the same in all cases.

The pre-binders are written `∀` though `α` sits under an `∃` in the update
underneath. This is the usual Iris reading: the implementation must work for
*every* state the resource might be in, and the update hands it *some* one of
them. Same binder, read from the two ends. -/

section Notation
open Lean

declare_syntax_cat awPre
declare_syntax_cat awPost
syntax "⟪ " ("∀ " ident+ ", ")? term " ⟫" : awPre
syntax "⟪ " ("∃ " ident+ ", ")? term " | " (ident+ ", ")? "RET " term ("; " term)? " ⟫" : awPost

syntax:max "AWP " ppRealFill(awPre ppSpace term:arg ppSpace term:arg " @ " term:arg
  ppSpace awPost) : term

open AeneasIris.AtomicP in
macro_rules
  | `(AWP ⟪ $[∀ $xs* , ]? $α:term ⟫ $Hd:term $t:term @ $E:term
          ⟪ $[∃ $ys* , ]? $β:term | $[$zs* , ]? RET $v:term $[; $post:term]? ⟫) => do
      let xs : List Ident := (xs.map (·.toList)).getD []
      let ys : List Ident := (ys.map (·.toList)).getD []
      let zs : List Ident := (zs.map (·.toList)).getD []
      let postTerm ← match post with
        | some p => `(some iprop($p))
        | none   => `((none : Option (IProp _)))
      let pre  (b : Term) : MacroM Term := buildAuLam xs b
      let mid  (b : Term) : MacroM Term := do buildAuLam xs (← buildAuLam ys b)
      let full (b : Term) : MacroM Term := do
        buildAuLam xs (← buildAuLam ys (← buildAuLam zs b))
      `(atomicWpi $Hd $t $E
          $(← pre  (← `(iprop($α))))
          $(← mid  (← `(iprop($β))))
          $(← full postTerm)
          $(← full v))

end Notation

/-! ## Display -/

section Delab
open Lean PrettyPrinter Delaborator SubExpr Aeneas.Std.Delab AeneasIris.AtomicP

/-- Peel a packed family whose leaf is an `Option`, returning the leaf only when
it is `some`. Used for `POST`, which is absent in most specs. -/
private def delabAuOptLeaf : DelabM (Option Term) :=
  enterAuChain #[] fun entries => do
    match_expr (← getExpr) with
    | Option.some _ _ => do
        let (_, body) ← delabBinders entries.toList (withNaryArg 1 delab)
        return some body
    | _ => return none

/-- `atomicWpi Hd t E α β POST f` → `AWP ⟪ ∀ x.., α ⟫ Hd t @ E ⟪ ∃ y.., β | z.., RET v; POST ⟫`.

Nothing in the packed term records where one binder group ends and the next
begins, so the boundaries are read off the *shorter* families: `α` binds exactly
the pre-binders, `β` those plus the post-binders, and `f` all three. -/
@[scoped delab app.AeneasIris.AtomicWpi.atomicWpi]
def delabAtomicWpi : Delab := do
  guard <| (← getExpr).isAppOfArity ``atomicWpi 15
  let Hd ← withNaryArg 8 delab
  let t  ← withNaryArg 9 delab
  let E  ← withNaryArg 10 delab
  let (preT, aBody) ← withNaryArg 11 delabAuFamily
  let (midT, bBody) ← withNaryArg 12 delabAuFamily
  let post          ← withNaryArg 13 delabAuOptLeaf
  let (allT, vBody) ← withNaryArg 14 delabAuFamily
  /- `f` must bind at least what `β` does, or these are not the families this
     notation builds; leave such a term to the default printer. -/
  guard <| preT.size ≤ midT.size && midT.size ≤ allT.size
  let xs ← toIdents preT
  let ys ← toIdents (midT.extract preT.size midT.size)
  let zs ← toIdents (allT.extract midT.size allT.size)
  let preStx ← if xs.isEmpty then `(awPre| ⟪ $aBody ⟫)
                             else `(awPre| ⟪ ∀ $xs*, $aBody ⟫)
  let postStx ← match ys.isEmpty, zs.isEmpty, post with
    | true,  true,  none   => `(awPost| ⟪ $bBody | RET $vBody ⟫)
    | true,  true,  some p => `(awPost| ⟪ $bBody | RET $vBody; $p ⟫)
    | true,  false, none   => `(awPost| ⟪ $bBody | $zs*, RET $vBody ⟫)
    | true,  false, some p => `(awPost| ⟪ $bBody | $zs*, RET $vBody; $p ⟫)
    | false, true,  none   => `(awPost| ⟪ ∃ $ys*, $bBody | RET $vBody ⟫)
    | false, true,  some p => `(awPost| ⟪ ∃ $ys*, $bBody | RET $vBody; $p ⟫)
    | false, false, none   => `(awPost| ⟪ ∃ $ys*, $bBody | $zs*, RET $vBody ⟫)
    | false, false, some p => `(awPost| ⟪ ∃ $ys*, $bBody | $zs*, RET $vBody; $p ⟫)
  `(AWP $preStx:awPre $Hd $t @ $E $postStx:awPost)

end Delab

/-! ## Round-trip tests

The three optional groups -- post-binders, `RET`-binders, `POST` -- are what the
reference needs separate macro rules for. Here they are one rule, so these check
that each combination still prints as what produced it. -/

section Tests
variable {Eff : Effect.{0}} (Hd : Handler Eff GF)
variable {S V : Type} (inv : S → V → IProp GF) (t : ITree Eff Nat)

/-- info: AWP ⟪ ∀ s v, inv s v ⟫ Hd t @ ⊤ ⟪ ∃ w, inv s w | r, RET r; inv s v ⟫ : IProp GF -/
#guard_msgs in
#check (AWP ⟪ ∀ s v, inv s v ⟫ Hd t @ ⊤ ⟪ ∃ w, inv s w | r, RET r; inv s v ⟫)

/-- info: AWP ⟪ ∀ s v, inv s v ⟫ Hd t @ ⊤ ⟪ ∃ w, inv s w | RET 0 ⟫ : IProp GF -/
#guard_msgs in
#check (AWP ⟪ ∀ s v, inv s v ⟫ Hd t @ ⊤ ⟪ ∃ w, inv s w | RET 0 ⟫)

/-- info: AWP ⟪ ∀ s v, inv s v ⟫ Hd t @ ⊤ ⟪ inv s v | RET 0 ⟫ : IProp GF -/
#guard_msgs in
#check (AWP ⟪ ∀ s v, inv s v ⟫ Hd t @ ⊤ ⟪ inv s v | RET 0 ⟫)

end Tests

end

end AeneasIris.AtomicWpi
