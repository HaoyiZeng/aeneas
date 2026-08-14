import Iris.BI.Lib.Atomic
import Iris.HeapLang.Lib.IInv
import AeneasIris.Wpi
import AeneasIris.Rules
import AeneasIris.AtomicWpi

/-! # One-shot logically atomic triples for `wpi`

```
⦃ P ⦄ ⟪ ∀ x, α ⟫ Hd m t @ E ⟪ ∃ y, β ⟫ ⦃ z : τ, RET v; POST ⦄
```

expands to

```
∀ Φ, P -∗ (|={⊤ \ E, ∅}=> ∃ x, α ∗ (∀ y, β -∗ |={∅, ⊤ \ E}=> ∀ z : τ, POST -∗ Φ v)) -∗
  wpi_mask GF Hd m t Φ ⊤
```

Ported from `sl-poc-haoyi`, which transcribes Perennial's `<<< >>>` triple
(`src/program_logic/atomic_fupd.v`), save for the `▷` they put in front of the
update.  That `▷` would let a caller supply the update one step late; nothing here
needs it, and a single-access implementation could not strip it anyway — the update
has to be open *before* the step, where no later is available.

Against `AtomicWpi.atomicWpi` the update has no abort branch, so `α` occurs only
positively and no greatest fixpoint is needed: the implementation gets one attempt at
the linearisation point rather than an unbounded retry loop.  A spinning
implementation still satisfies such a triple, by opening a persistent invariant to see
whether the attempt will succeed and only then opening the update.

This is **notation only**.  There is no constant and no telescopes: the binders expand
to iterated `∃`/`∀`, so the triple simply *is* its unfolding.  Proofs need nothing
beyond the ordinary fupd and invariant lemmas, and — unlike `atomicWpi`, which must be
unfolded with `simp only [atomicWpi]` before anything can look at it — a tactic can
read the shape directly.

`P` is an ordinary precondition, handed over before the operation starts.  `β` is what
every thread observes at the linearisation point.  `POST` is the caller's private
receipt, and only it may mention `z`, a value the implementation chooses.

The multi-shot triples of `AtomicWpi` share the angle brackets and are told apart by
their postcondition: theirs always carries `| RET …` inside the angles, this one never
does.
-/

namespace AeneasIris.OneShotWpi

open Iris BI Aeneas.Data.Coinductive AeneasIris

section Spec

variable {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]
variable {Eff : Effect.{1}} {V : Type} {A B P : Type}

open AeneasIris.AtomicWpi (wandM)

/-- A one-shot logically atomic specification, as a **constant**.

The notation below is the readable surface; this is the same statement as a
definition, which is what lets it be *quantified over*: `iSpec_of_IASpec` turns
any `IASpec` into an ordinary triple, so an operation needs only its atomic
specification and the sequential one comes for free.  `analyse` can also key on
it, exactly as it already does on `iSpec`. -/
def IASpec (Hd : Handler Eff GF) (m : Mode) (Pre : IProp GF) (t : ITree Eff V)
    (E : CoPset) (α : A → IProp GF) (β : A → B → IProp GF)
    (POST : A → B → P → IProp GF) (f : A → B → P → V) : Prop :=
  ⊢ iprop(∀ Φ : Post GF V, Pre -∗
      (|={⊤ \ E, ∅}=> ∃ x, α x ∗
        (∀ y, β x y -∗ |={∅, ⊤ \ E}=> ∀ z, POST x y z -∗ Φ (f x y z))) -∗
      wpi_mask GF Hd m t Φ ⊤)

/-- **An atomic specification is also a sequential one.**  A caller that simply
owns `α x` can discharge the update itself -- shrink the mask, hand the resource
over, take `β x y` back, restore -- so the atomic statement subsumes the ordinary
triple and only the former need be proved. -/
theorem iSpec_of_IASpec {Hd : Handler Eff GF} {m : Mode} {Pre : IProp GF}
    {t : ITree Eff V} {E : CoPset} {α : A → IProp GF} {β : A → B → IProp GF}
    {POST : A → B → P → IProp GF} {f : A → B → P → V}
    (h : IASpec Hd m Pre t E α β POST f) (x : A) :
    ⊢ iprop(Pre -∗ α x -∗
        wpi_mask GF Hd m t
          (fun r => iprop(∃ y z, ⌜r = f x y z⌝ ∗ β x y ∗ POST x y z)) ⊤) := by
  unfold IASpec at h
  iintro HPre Hα
  ihave Hspec := h
  iapply Hspec $$ %_ HPre
  imod (Iris.fupd_mask_subseteq (E2 := (∅ : CoPset))
         (fun _ hx => absurd hx Iris.Std.LawfulSet.mem_empty)) with Hback
  iexists x
  isplitl [Hα]
  · iexact Hα
  · imodintro
    iintro %y Hβ
    imod Hback
    imodintro
    iintro %z HPost
    iexists y
    iexists z
    isplitr [Hβ HPost]
    · itrivial
    · isplitl [Hβ]
      · iexact Hβ
      · iexact HPost

/-- `IASpec` as an entailment, which is the shape `irule` can apply: the ordinary
precondition is framed out of the context and the update is left as a goal. -/
theorem IASpec.wand {Hd : Handler Eff GF} {m : Mode} {Pre : IProp GF}
    {t : ITree Eff V} {E : CoPset} {α : A → IProp GF} {β : A → B → IProp GF}
    {POST : A → B → P → IProp GF} {f : A → B → P → V}
    (h : IASpec Hd m Pre t E α β POST f) (Φ : Post GF V) :
    ⊢ iprop(Pre -∗
        (|={⊤ \ E, ∅}=> ∃ x, α x ∗
          (∀ y, β x y -∗ |={∅, ⊤ \ E}=> ∀ z, POST x y z -∗ Φ (f x y z))) -∗
        wpi_mask GF Hd m t Φ ⊤) := by
  unfold IASpec at h
  iintro HPre HU
  ihave Hspec := h
  iapply Hspec $$ %_ HPre HU

end Spec

section Notation
open Lean

declare_syntax_cat osPre
declare_syntax_cat osAtomicPost
declare_syntax_cat osPost

syntax "⟪" ("∀ " ident+ ", ")* term "⟫" : osPre
syntax "⟪" ("∃ " ident+ ", ")* term "⟫" : osAtomicPost
syntax " ⦃ " (ident " : " term ", ")? "RET " term ("; " term)? " ⦄ " : osPost

syntax (name := oneShotTripleNotation)
  ppRealFill((" ⦃ " term " ⦄ ")? osPre ppSpace term:arg ppSpace term:arg ppSpace term:arg
    " @ " term:arg ppSpace osAtomicPost ppSpace osPost) : term

macro_rules
  | `($[⦃ $P:term ⦄]? ⟪ $[∀ $xs:ident*,]* $α:term ⟫ $Hd:term $m:term $t:term @ $E:term
      ⟪ $[∃ $ys:ident*,]* $β:term ⟫
      ⦃ $[$z:ident : $zty:term,]? RET $v:term $[; $POST:term]? ⦄) => do
      /- Pack the binder groups into `IASpec`'s single arguments with `buildAuLam`,
      exactly as the multi-shot notation does: the surface syntax stays flexible
      while the constant stays first-order. -/
      let xs : List Ident := (xs.flatMap id).toList
      let ys : List Ident := (ys.flatMap id).toList
      let zs : List Ident := match z with | some z => [z] | none => []
      let pre  (b : Term) : MacroM Term := buildAuLam xs b
      let mid  (b : Term) : MacroM Term := do buildAuLam xs (← buildAuLam ys b)
      let full (b : Term) : MacroM Term := do
        buildAuLam xs (← buildAuLam ys (← buildAuLam zs b))
      let postTerm ← match POST with
        | some Q => `(iprop($Q))
        | none   => `(iprop(True))
      let preTerm ← match P with
        | some Pt => `(iprop($Pt))
        | none    => `(iprop(emp))
      `(IASpec $Hd $m $preTerm $t $E
          $(← pre  (← `(iprop($α))))
          $(← mid  (← `(iprop($β))))
          $(← full postTerm)
          $(← full v))

end Notation

/-! ## Opening an invariant to discharge the update

The update a one-shot triple asks for is an ordinary fupd, so the ordinary
`iinv … with …` opens an invariant into it -- the same tactic a sequential
specification uses.  What is left over is bookkeeping: `iinv` lands at `E \ ↑N`
while the update wants `∅`, so the mask has to be shrunk and later restored.
`iinv_atomic` does the opening and the shrinking together, and leaves the closer
of each in scope.
-/

section Tactic
open Lean

/-- `iinv_atomic h with ⟨pat, cl⟩ back bk` opens the invariant `h` into the update
of a one-shot triple, exactly as `iinv h with ⟨pat, cl⟩` does, and additionally
shrinks the mask to the `∅` the update asks for.  `cl` re-closes the invariant and
`bk` restores the mask; once the operation's resource has been handed back,
discharge them in that order — `imod bk`, then `iapply cl`. -/
macro "iinv_atomic " h:ident " with " pat:icasesPat " back " bk:ident : tactic =>
  `(tactic|
    (iinv $h:ident with $pat
     imod (Iris.fupd_mask_subseteq (E2 := (∅ : CoPset))
            (fun _ hx => absurd hx Iris.Std.LawfulSet.mem_empty)) with $bk:ident))

end Tactic

/-! ## Smoke tests

These only check that the `macro_rule` elaborates; they assert nothing. -/

section Smoke
variable {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]
variable {Eff : Effect.{1}} {V : Type} {Hd : Handler Eff GF} {m : Mode}
variable (t : ITree Eff V) (E : CoPset) (v : V)
variable (P Q R : IProp GF) (Pn : Nat → IProp GF) (Qm : Nat → IProp GF)
variable (Rk : Nat → IProp GF) (g : Nat → V)

example : Prop := ⟪ P ⟫ Hd m t @ E ⟪ Q ⟫ ⦃ RET v ⦄
example : Prop := ⟪ ∀ n, Pn n ⟫ Hd m t @ E ⟪ Q ⟫ ⦃ RET v ⦄
example : Prop := ⟪ ∀ n, Pn n ⟫ Hd m t @ E ⟪ ∃ k, Qm k ⟫ ⦃ RET v ⦄
example : Prop := ⟪ ∀ n, Pn n ⟫ Hd m t @ E ⟪ Q ⟫ ⦃ RET v; R ⦄
example : Prop := ⟪ ∀ n, Pn n ⟫ Hd m t @ E ⟪ Q ⟫ ⦃ k : Nat, RET g k; Rk k ⦄
example : Prop := ⦃ P ⦄ ⟪ Q ⟫ Hd m t @ E ⟪ R ⟫ ⦃ RET v ⦄
example : Prop := ⦃ P ∗ Q ⦄ ⟪ ∀ n, Pn n ⟫ Hd m t @ E ⟪ ∃ k, Qm k ⟫ ⦃ k : Nat, RET g k; Rk k ⦄

end Smoke

end AeneasIris.OneShotWpi
