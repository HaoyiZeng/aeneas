import AeneasIris.OneShotWpi
namespace Chk
open Iris BI Aeneas.Data.Coinductive AeneasIris AeneasIris.OneShotWpi
variable {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]
variable {Eff : Effect.{1}} {V : Type} {A B P : Type}
variable {Hd : Handler Eff GF} {m : Mode}

/-- The graded accessor, stated on its own. -/
def gacc (Eo Ei : CoPset) {X Y : Type}
    (α : X → IProp GF) (β γ : X → Y → IProp GF) : IProp GF :=
  iprop(|={Eo,Ei}=> ∃ x, α x ∗ (∀ y, β x y -∗ |={Ei,Eo}=> γ x y))

/-- `IASpec` is exactly "a natural transformation from `gacc` to `wpi`".
`rfl` decides it. -/
theorem IASpec_is_nat_transf (Pre : IProp GF) (t : ITree Eff V) (E : CoPset)
    (α : A → IProp GF) (β : A → B → IProp GF)
    (POST : A → B → P → IProp GF) (f : A → B → P → V) :
    IASpec Hd m Pre t E α β POST f
    = (⊢ iprop(∀ Φ : Post GF V, Pre -∗
        gacc (⊤ \ E) ∅ α β (fun x y => iprop(∀ z, POST x y z -∗ Φ (f x y z)))
        -∗ wpi_mask GF Hd m t Φ ⊤)) := rfl

end Chk
