import AeneasIris.Effects.AtomicHeapAPI
import AeneasIris.Tactics.Core

/-! Accessors as first-class terms: composition instead of elimination. -/

namespace AccLib

open Iris BI Aeneas.Data.Coinductive
open AeneasIris AeneasIris.Heap AeneasIris.HeapAPI AeneasIris.AtomicHeapAPI
open Aeneas.Std (Loc)
open scoped AeneasIris.OneShotWpi

variable {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF] [G : HeapGS.{0} GF]

/-- An accessor with no positions: hand over `S`, get `A`, return `B`, get `T`. -/
abbrev Acc0 (Eo Ei : CoPset) (S A B T : IProp GF) : Prop :=
  S ⊢ iprop(|={Eo,Ei}=> A ∗ (B -∗ |={Ei,Eo}=> T))

/-- A graded, dependent accessor.  The residual is hidden by the wand; the grade
records what was opened. -/
abbrev Acc (Eo Ei : CoPset) (S : IProp GF) {X Y : Type}
    (α : X → IProp GF) (β γ : X → Y → IProp GF) : Prop :=
  S ⊢ iprop(|={Eo,Ei}=> ∃ x, α x ∗ (∀ y, β x y -∗ |={Ei,Eo}=> γ x y))

/-- Access under an unpositioned accessor.  This is the composition law: the two
closers are consumed here, once, and the composite exposes one. -/
theorem Acc.under {X Y : Type} {Eo Em Ei : CoPset} {S A B T : IProp GF}
    {α : X → IProp GF} {β δ : X → Y → IProp GF}
    (H₁ : Acc0 Eo Em S A B T)
    (H₂ : Acc Em Ei A α β (fun x y => iprop(B ∗ δ x y))) :
    Acc Eo Ei S α β (fun x y => iprop(T ∗ δ x y)) := by
  unfold Acc0 at H₁; unfold Acc at H₂ ⊢
  refine .trans H₁ ?_
  iintro HS
  imod HS with ⟨HA, Hback⟩
  ihave HI := H₂ $$ HA
  imod HI with ⟨%x, Hf, Hin⟩
  imodintro
  iexists x
  isplitl [Hf]
  · iexact Hf
  · iintro %y HB
    ihave HR := Hin $$ %y HB
    imod HR with ⟨HBb, Hd⟩
    ihave HT := Hback $$ HBb
    imod HT with HT
    imodintro
    isplitl [HT]
    · iexact HT
    · iexact Hd

/-- Composition of accessors, as a term-level operator. -/
scoped infixl:55 " ⨟₀ " => Acc0.comp
scoped infixl:55 " ⨟ "  => Acc.under

/-- An Iris invariant is an accessor. -/
theorem Acc0.ofInv {E : CoPset} {N : Namespace} {P : IProp GF} (Hsub : ↑N ⊆ E) :
    Acc0 E (E \ ↑N) (Iris.inv N P) iprop(▷ P) iprop(▷ P) iprop(True) := by
  unfold Acc0
  iintro HI
  iapply (Iris.inv_acc Hsub) $$ HI

/-- Shrinking the mask is an accessor too. -/
theorem Acc0.shrink {Eo Ei : CoPset} (Hsub : Ei ⊆ Eo) (S : IProp GF) :
    Acc0 Eo Ei S S S S := by
  unfold Acc0
  iintro HS
  imod (Iris.fupd_mask_subseteq Hsub) with Hback
  imodintro
  isplitl [HS]
  · iexact HS
  · iintro HS'
    imod Hback
    imodintro
    iexact HS' 

/-- Composition of unpositioned accessors. -/
theorem Acc0.comp {Eo Em Ei : CoPset} {S A B T X Y : IProp GF}
    (H₁ : Acc0 Eo Em S A B T) (H₂ : Acc0 Em Ei A X Y B) : Acc0 Eo Ei S X Y T := by
  unfold Acc0 at H₁ H₂ ⊢
  refine .trans H₁ ?_
  iintro HS
  imod HS with ⟨HA, Hback⟩
  ihave HX := H₂ $$ HA
  imod HX with ⟨HXf, Hin⟩
  imodintro
  isplitl [HXf]
  · iexact HXf
  · iintro HY
    ihave HB := Hin $$ HY
    imod HB with HB
    iapply Hback $$ HB

/-- Focus a cell out of an invariant body.  `hβ` is the client's one real
obligation: whatever is written back re-establishes the invariant.  The body is
the residual and is never named again. -/
theorem Acc.focus_ex {Y : Type} {E : CoPset} (l : Loc) (φ : Nat → Prop)
    (β : Nat → Y → IProp GF)
    (hβ : ∀ v y, φ v → β v y ⊢ iprop(∃ v' : Nat, l ↦ v' ∗ ⌜φ v'⌝)) :
    Acc (GF := GF) E E iprop(▷ ∃ v : Nat, l ↦ v ∗ ⌜φ v⌝)
        (fun v => iprop(l ↦ v)) β
        (fun v _ => iprop((▷ ∃ v : Nat, l ↦ v ∗ ⌜φ v⌝) ∗ ⌜φ v⌝)) := by
  unfold Acc
  iintro HP
  imod HP with ⟨%v, Hl, %hv⟩
  imodintro
  iexists v
  isplitl [Hl]
  · iexact Hl
  · iintro %y Hb
    imodintro
    isplitl [Hb]
    · inext
      iapply (hβ v y hv) $$ Hb
    · ipureintro; exact hv

/-- The identity accessor: the body of an accessor *is* an accessor from itself.
This is what lets a caller's atomic update be treated as an `Acc`. -/
theorem Acc.id {X Y : Type} {Eo Ei : CoPset}
    {α : X → IProp GF} {β γ : X → Y → IProp GF} :
    Acc Eo Ei iprop(|={Eo,Ei}=> ∃ x, α x ∗ (∀ y, β x y -∗ |={Ei,Eo}=> γ x y)) α β γ :=
  .rfl

/-- **Change of interface.**  `g` maps positions forward and `h` maps directions
back, depending on the position -- a Dialectica morphism.  The three coherence
conditions say the concrete interface refines the abstract one.

This is the law a *derived* operation needs: the caller hands over an accessor at
the abstract interface, and the primitive it calls wants one at the concrete
interface.  `recast` is the translation, and it opens nothing. -/
theorem Acc.recast {X X' Y Y' : Type} {Eo Ei : CoPset} {S : IProp GF}
    {α : X → IProp GF} {β γ : X → Y → IProp GF}
    {α' : X' → IProp GF} {β' γ' : X' → Y' → IProp GF}
    (g : X → X') (h : X → Y' → Y)
    (hα : ∀ x, α x ⊢ α' (g x))
    (hβ : ∀ x y', β' (g x) y' ⊢ β x (h x y'))
    (hγ : ∀ x y', γ x (h x y') ⊢ γ' (g x) y')
    (H : Acc Eo Ei S α β γ) : Acc Eo Ei S α' β' γ' := by
  unfold Acc at H ⊢
  refine .trans H ?_
  iintro HS
  imod HS with ⟨%x, Hf, Hback⟩
  imodintro
  iexists (g x)
  ihave Hf' := (hα x) $$ Hf
  isplitl [Hf']
  · iexact Hf'
  · iintro %y' Hb'
    ihave Hb := (hβ x y') $$ Hb'
    ihave HG := Hback $$ %(h x y') Hb
    imod HG with HG
    imodintro
    iapply (hγ x y') $$ HG

/-- An accessor may be weakened in its result: this is where a client turns what
the composite gives back into what a specification asks for. -/
theorem Acc.mono {X Y : Type} {Eo Ei : CoPset} {S : IProp GF}
    {α : X → IProp GF} {β γ γ' : X → Y → IProp GF}
    (H : Acc Eo Ei S α β γ) (h : ∀ x y, γ x y ⊢ γ' x y) : Acc Eo Ei S α β γ' := by
  unfold Acc at H ⊢
  refine .trans H ?_
  iintro HS
  imod HS with ⟨%x, Hf, Hback⟩
  imodintro
  iexists x
  isplitl [Hf]
  · iexact Hf
  · iintro %y HB
    ihave HG := Hback $$ %y HB
    imod HG with HG
    imodintro
    iapply (h x y) $$ HG

/-- Writing back any value that satisfies `φ` re-establishes a cell invariant.
This is the shape almost every `hβ` obligation takes. -/
theorem cell_keep (l : Loc) (φ : Nat → Prop) (v : Nat) (h : φ v) :
    (iprop(l ↦ v) : IProp GF) ⊢ iprop(∃ v' : Nat, l ↦ v' ∗ ⌜φ v'⌝) := by
  iintro Hl
  iexists v
  isplitl [Hl]
  · iexact Hl
  · ipureintro; exact h

/-- The accessor a client gets from a cell invariant.  Composition happens here,
once and for all: opening, shrinking and focusing are three accessors and this is
their composite.  A client never sees a closer, a mask or the invariant body. -/
theorem Acc.cellInv {Y : Type} {N : Namespace} {l : Loc} {φ : Nat → Prop}
    {β : Nat → Y → IProp GF}
    (hβ : ∀ v y, φ v → β v y ⊢ iprop(∃ v' : Nat, l ↦ v' ∗ ⌜φ v'⌝)) :
    Acc (GF := GF) (⊤ \ ∅) ∅ (Iris.inv N iprop(∃ v : Nat, l ↦ v ∗ ⌜φ v⌝))
        (fun v => iprop(l ↦ v)) β (fun v _ => iprop(⌜φ v⌝)) :=
  Acc.mono
    (Acc.under
      (Acc0.comp (Acc0.ofInv (by simp))
                 (Acc0.shrink (fun _ hx => absurd hx Iris.Std.LawfulSet.mem_empty) _))
      (Acc.focus_ex l φ β hβ))
    (by intro x y; iintro ⟨-, %hx⟩; ipureintro; exact hx)

/-- The read-only case: whatever was read is written back unchanged.  This needs
no obligation from the client, so it is a single token at the use site. -/
theorem Acc.cellInv_ro {Y : Type} {N : Namespace} {l : Loc} {φ : Nat → Prop} :
    Acc (GF := GF) (⊤ \ ∅) ∅ (Iris.inv N iprop(∃ v : Nat, l ↦ v ∗ ⌜φ v⌝))
        (fun v => iprop(l ↦ v)) (fun v (_ : Y) => iprop(l ↦ v))
        (fun v _ => iprop(⌜φ v⌝)) :=
  Acc.cellInv (fun v _ h => cell_keep l φ v h)

/-- `iacc H with acc` discharges an atomic update using the accessor `acc`, which
the hypothesis `H` provides.  Nothing of the accessor is exposed: two goals are
left: any `?_` written inside `acc`, and finally the step from what the accessor
returns to the specification's postcondition. -/
macro "iacc " h:specPat " with " t:term : tactic =>
  `(tactic| iapply (AccLib.Acc.mono $t ?_) $$ $h)

end AccLib
