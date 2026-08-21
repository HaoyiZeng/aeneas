import Iris.BI
import Iris.BI.Lib.Atomic
import Iris.ProofMode.Tactics
import Iris.Instances.Lib.Invariants

namespace AccComp
open Iris Iris.BI

variable {PROP : Type _} [BI PROP]

/-- An accessor from `S`: hand over `S`, get the focus `A`, and on returning `B`
get `T` back.  The residual is hidden by the wand. -/
abbrev acc (A B T : PROP) : PROP := iprop(A ∗ (B -∗ T))

/-- Composition.  This is the law Iris has no instance of. -/
theorem acc_comp (S A B T X Y : PROP)
    (h₁ : S ⊢ acc A B T) (h₂ : A ⊢ acc X Y B) :
    S ⊢ acc X Y T := by
  refine .trans h₁ ?_
  iintro ⟨HA, Hback⟩
  ihave ⟨HX, Hin⟩ := h₂ $$ HA
  isplitl [HX]
  · iexact HX
  · iintro HY
    iapply Hback
    iapply Hin $$ HY


/-! ## The dependent accessor -/

/-- Positions `x`, directions `y`, and a result that depends on both.
This is the shape of a Dialectica morphism. -/
def dacc {X Y : Type} (α : X → PROP) (β γ : X → Y → PROP) : PROP :=
  iprop(∃ x, α x ∗ (∀ y, β x y -∗ γ x y))

/-- Composition of dependent accessors.

`h` maps an inner direction back to an outer one, depending on both positions --
which is exactly Dialectica's contravariant map on directions.  Positions compose
forwards (into a pair); directions compose backwards through `h`. -/
theorem dacc_comp {X Y X' Y' : Type} (S : PROP)
    (α : X → PROP) (β γ : X → Y → PROP)
    (α' : X → X' → PROP) (β' : X → X' → Y' → PROP)
    (h : X → X' → Y' → Y)
    (H₁ : S ⊢ dacc α β γ)
    (H₂ : ∀ x, α x ⊢ dacc (α' x) (β' x) (fun x' y' => β x (h x x' y'))) :
    S ⊢ dacc (X := X × X') (Y := Y')
      (fun p => α' p.1 p.2)
      (fun p y' => β' p.1 p.2 y')
      (fun p y' => γ p.1 (h p.1 p.2 y')) := by
  unfold dacc at H₂ ⊢
  refine .trans H₁ ?_
  unfold dacc
  iintro ⟨%x, HA, Hback⟩
  ihave HI := H₂ x $$ HA
  icases HI with ⟨%x', HX, Hin⟩
  iexists (x, x')
  isplitl [HX]
  · iexact HX
  · iintro %y' HY
    ihave HB := Hin $$ %y' HY
    iapply Hback $$ %(h x x' y') HB

section Graded
variable [BIFUpdate PROP]

/-- The graded accessor: opening moves the mask `Eo → Ei`, closing moves it back. -/
abbrev gacc (Eo Ei : CoPset) (A B T : PROP) : PROP :=
  iprop(|={Eo,Ei}=> A ∗ (B -∗ |={Ei,Eo}=> T))

/-- Graded composition.  The masks compose because `fupd` is a parameterised
monad: `Eo → Em` then `Em → Ei` on the way in, and the reverse on the way out. -/
theorem gacc_comp (Eo Em Ei : CoPset) (S A B T X Y : PROP)
    (h₁ : S ⊢ gacc Eo Em A B T) (h₂ : A ⊢ gacc Em Ei X Y B) :
    S ⊢ gacc Eo Ei X Y T := by
  refine .trans h₁ ?_
  iintro HS
  imod HS with ⟨HA, Hback⟩
  ihave HXin := h₂ $$ HA
  imod HXin with ⟨HX, Hin⟩
  imodintro
  isplitl [HX]
  · iexact HX
  · iintro HY
    ihave HB' := Hin $$ HY
    imod HB' with HB
    iapply Hback $$ HB

end Graded


section Instances
open Iris.Std
variable {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]

/-- Iris's invariant opening is literally a graded accessor. -/
theorem inv_is_gacc {E : CoPset} {N : Namespace} {P : IProp GF} (Hsub : ↑N ⊆ E) :
    ⊢ (Iris.inv N P : IProp GF) -∗
      gacc E (E \ ↑N) iprop(▷ P) iprop(▷ P) iprop(True) := by
  iintro HI
  iapply (Iris.inv_acc Hsub) $$ HI

/-- And Iris's atomic accessor is one too, once the abort branch is dropped:
`gacc` is exactly the one-shot fragment of `atomicAcc`. -/
theorem atomicAcc_is_gacc {A B : Type} (Eo Ei : CoPset)
    (α : A → IProp GF) (Pa : IProp GF) (β Φ : A → B → IProp GF) :
    Iris.atomicAcc Eo Ei α Pa β Φ ⊢
      iprop(|={Eo,Ei}=> ∃ x, α x ∗ (∀ y, β x y -∗ |={Ei,Eo}=> Φ x y)) := by
  unfold Iris.atomicAcc
  iintro HA
  imod HA with ⟨%x, Hα, Hch⟩
  imodintro
  iexists x
  isplitl [Hα]
  · iexact Hα
  · icases Hch with ⟨-, Hcommit⟩
    iexact Hcommit

end Instances

end AccComp
