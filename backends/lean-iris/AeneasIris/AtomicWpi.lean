import Iris.BI.Lib.Atomic
import AeneasIris.Wpi
import AeneasIris.Rules

/-! # Logically atomic triples for `wpi` -/

namespace AeneasIris.AtomicWpi

open Iris BI Aeneas.Data.Coinductive AeneasIris

section

variable {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]

/-- `P -∗? Q` is `Q` when there is no `P`. -/
def wandM (P : Option (IProp GF)) (Q : IProp GF) : IProp GF :=
  match P with
  | some P => iprop(P -∗ Q)
  | none   => Q

@[simp] theorem wandM_none (Q : IProp GF) : wandM none Q = Q := rfl
@[simp] theorem wandM_some (P Q : IProp GF) : wandM (some P) Q = iprop(P -∗ Q) := rfl

/-- A logically atomic triple. -/
def atomicWpi {Eff : Effect.{u}} {V : Type v} {A B P : Type _}
    (Hd : Handler Eff GF) (m : Mode) (t : ITree Eff V) (E : CoPset)
    (α : A → IProp GF) (β : A → B → IProp GF)
    (POST : A → B → P → Option (IProp GF)) (f : A → B → P → V) : IProp GF :=
  iprop(∀ Φ : Post GF V,
    atomicUpdate (⊤ \ E) ∅ α β (fun x y => iprop(∀ z, wandM (POST x y z) (Φ (f x y z)))) -∗
    wpi_mask GF Hd m t Φ ⊤)

/-! ## Notation -/

section Notation
open Lean

declare_syntax_cat awPre
declare_syntax_cat awPost
syntax "⟪ " ("∀ " ident+ ", ")? term " ⟫" : awPre
syntax "⟪ " ("∃ " ident+ ", ")? term " | " (ident+ ", ")? "RET " term ("; " term)? " ⟫" : awPost

syntax:max ppRealFill(awPre ppSpace term:arg ppSpace term:arg ppSpace term:arg
  " @ " term:arg ppSpace awPost) : term

macro_rules
  | `(⟪ $[∀ $xs* , ]? $α:term ⟫ $Hd:term $m:term $t:term @ $E:term
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
      `(atomicWpi $Hd $m $t $E
          $(← pre  (← `(iprop($α))))
          $(← mid  (← `(iprop($β))))
          $(← full postTerm)
          $(← full v))

end Notation

/-! ## Display -/

section Delab
open Lean PrettyPrinter Delaborator SubExpr Iris.Delab

/-- Like `Iris.Delab.enterUncurryChain`, but silent about the binder that -/
private partial def enterAuChain (acc : Array BinderEntry)
    (k : Array BinderEntry → DelabM α) : DelabM α := do
  match (← getExpr) with
  | .lam n ty b _ =>
    if ty.isConstOf ``Unit && !b.hasLooseBVars then
      withBindingBody' n pure fun _ => enterAuChain acc k
    else
      let pos ← getPos
      withBindingBody' n pure fun fv => enterAuChain (acc.push (fv.fvarId!, n, pos)) k
  | e =>
    if e.isAppOfArity ``Iris.auUncurry 4 then withAppArg <| enterAuChain acc k
    else k acc

/-- Peel a packed family into `(binders, body)`. -/
private def delabAuFamily : DelabM (Array Term × Term) :=
  enterAuChain #[] fun entries => delabBinders entries.toList delab

/-- The notation takes identifiers, so anything `delabBinders` turned into a -/
private def toIdents (ts : Array Term) : DelabM (Array Ident) :=
  ts.mapM fun t => if t.raw.isIdent then pure ⟨t.raw⟩ else failure

/-- Peel a packed family whose leaf is an `Option`, returning the leaf only when it is `some`. -/
private def delabAuOptLeaf : DelabM (Option Term) :=
  enterAuChain #[] fun entries => do
    match_expr (← getExpr) with
    | Option.some _ _ => do
        let (_, body) ← delabBinders entries.toList (withNaryArg 1 delab)
        return some body
    | _ => return none

/-- `atomicWpi Hd m t E α β POST f` → `⟪ ∀ x.., α ⟫ Hd m t @ E ⟪ ∃ y.., β | z.., RET v; POST ⟫`. -/
@[scoped delab app.AeneasIris.AtomicWpi.atomicWpi]
def delabAtomicWpi : Delab := do
  guard <| (← getExpr).isAppOfArity ``atomicWpi 16
  let Hd ← withNaryArg 8 delab
  let m  ← withNaryArg 9 delab
  let t  ← withNaryArg 10 delab
  let E  ← withNaryArg 11 delab
  let (preT, aBody) ← withNaryArg 12 delabAuFamily
  let (midT, bBody) ← withNaryArg 13 delabAuFamily
  let post          ← withNaryArg 14 delabAuOptLeaf
  let (allT, vBody) ← withNaryArg 15 delabAuFamily
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
  `($preStx:awPre $Hd $m $t @ $E $postStx:awPost)

end Delab

/-! ## Opening the update without leaving `wpi_mask` -/

/-- Discharge the mask side condition of the `aupd` lemmas. -/
syntax "aupd_mask" : tactic
macro_rules
  | `(tactic| aupd_mask) =>
    `(tactic| first
      | assumption
      | simp
      | exact fun _ _ => Iris.Std.CoPset.mem_full
      | intro _ _; simp)

section Aupd

open AeneasIris

variable {Eff : Effect.{1}} {V : Type} {Hd : Handler Eff GF} {m : Mode}

/-- **At the empty mask, `wpi_mask` is `wpi`.** -/
theorem wpi_mask_empty (t : ITree Eff V) (Φ : Post GF V) :
    wpi_mask GF Hd m t Φ ∅ ⊣⊢ wpi GF Hd m t Φ := by
  simp only [wpi_mask]
  exact (AeneasIris.wpi_update_emp (H := Hd) t _).trans
    (AeneasIris.wpi_update_post_emp (H := Hd) t Φ)

/-- **Open the atomic update and commit, in one step.** -/
theorem wpi_aupd_commit {A B : Type _} (Eo Ei E : CoPset) (t : ITree Eff V)
    (α : A → IProp GF) (β Ψ : A → B → IProp GF) (Φ : Post GF V)
    (hsub : Eo ⊆ E) :
    atomicUpdate Eo Ei α β Ψ ⊢
      iprop((∀ x, α x -∗ wpi_mask GF Hd m t (fun v => iprop(∃ y, β x y ∗ (Ψ x y -∗ Φ v))) Ei) -∗
            wpi_mask GF Hd m t Φ E) := by
  iintro HAU Hbody
  iapply (AeneasIris.wpi_reduce_mask (H := Hd) t Φ E Ei)
  imod (Iris.aupd_acc _ _ _ Eo Ei E hsub) $$ HAU with ⟨%x, Hα, Hclose⟩
  imodintro
  icases Hclose with ⟨-, Hcommit⟩
  iapply (AeneasIris.wpi_wand (H := Hd) t
            (fun v => iprop(∃ y, β x y ∗ (Ψ x y -∗ Φ v)))
            (fun v => iprop(|={Ei, E}=> Φ v)) Ei) $$ [Hcommit]
  · iintro %v ⟨%y, Hβ, Hret⟩
    imod Hcommit $$ Hβ with HΨ
    imodintro
    iapply Hret $$ HΨ
  · iapply Hbody $$ Hα

/-- **Open the atomic update and abort.** -/
theorem wpi_aupd_abort {A B : Type _} (Eo Ei E : CoPset) (t : ITree Eff V)
    (α : A → IProp GF) (β Ψ : A → B → IProp GF) (Φ : Post GF V)
    (hsub : Eo ⊆ E) :
    atomicUpdate Eo Ei α β Ψ ⊢
      iprop((∀ x, α x -∗ wpi_mask GF Hd m t
                    (fun v => iprop(α x ∗ (atomicUpdate Eo Ei α β Ψ -∗ Φ v))) Ei) -∗
            wpi_mask GF Hd m t Φ E) := by
  iintro HAU Hbody
  iapply (AeneasIris.wpi_reduce_mask (H := Hd) t Φ E Ei)
  imod (Iris.aupd_acc _ _ _ Eo Ei E hsub) $$ HAU with ⟨%x, Hα, Hclose⟩
  imodintro
  icases Hclose with ⟨Habort, -⟩
  iapply (AeneasIris.wpi_wand (H := Hd) t
            (fun v => iprop(α x ∗ (atomicUpdate Eo Ei α β Ψ -∗ Φ v)))
            (fun v => iprop(|={Ei, E}=> Φ v)) Ei) $$ [Habort]
  · iintro %v ⟨Hα', Hret⟩
    imod Habort $$ Hα' with HAU'
    imodintro
    iapply Hret $$ HAU'
  · iapply Hbody $$ Hα

/-! ### Opening, at any arity -/

syntax "iaupd_commit " specPat " as " rcasesPat " with " introPat : tactic
syntax "iaupd_abort " specPat " as " rcasesPat " with " introPat : tactic

open Lean in
/-- Open the atomic update, naming the update's binders.

A single-identifier pattern is introduced *directly*, rather than introduced under
an internal name and then `obtain`ed: `obtain x := v` on a bare local variable is
a no-op, so the requested name would be accepted and then silently dropped.  A
tuple pattern still goes through `obtain`, which destructures the variable in
place and so substitutes into the hypotheses already in scope. -/
macro_rules
  | `(tactic| iaupd_commit $au:specPat as $pat:rcasesPat with $h:introPat) => do
      if pat.raw.getKind == ``Lean.Parser.Tactic.rcasesPat.one then
        let id : Ident := ⟨pat.raw[0]⟩
        let bi ← `(Lean.binderIdent| $id:ident)
        `(tactic|
          (iapply (wpi_aupd_commit (hsub := by aupd_mask)) $$ $au
           iintro %$bi $h))
      else
        `(tactic|
          (iapply (wpi_aupd_commit (hsub := by aupd_mask)) $$ $au
           iintro %iaupdPacked $h
           obtain $pat := iaupdPacked))
  | `(tactic| iaupd_abort $au:specPat as $pat:rcasesPat with $h:introPat) => do
      if pat.raw.getKind == ``Lean.Parser.Tactic.rcasesPat.one then
        let id : Ident := ⟨pat.raw[0]⟩
        let bi ← `(Lean.binderIdent| $id:ident)
        `(tactic|
          (iapply (wpi_aupd_abort (hsub := by aupd_mask)) $$ $au
           iintro %$bi $h))
      else
        `(tactic|
          (iapply (wpi_aupd_abort (hsub := by aupd_mask)) $$ $au
           iintro %iaupdPacked $h
           obtain $pat := iaupdPacked))

end Aupd

/-! ## One-shot atomic updates -/

section OneShot

open AeneasIris

variable {Eff : Effect.{1}} {V : Type} {Hd : Handler Eff GF} {m : Mode}

/-- A one-shot atomic update: hands over `α x`, takes back `β x y`, returns `Ψ x y`. -/
def oneShotUpd {A B : Type _} (Eo Ei : CoPset)
    (α : A → IProp GF) (β Ψ : A → B → IProp GF) : IProp GF :=
  iprop(|={Eo, Ei}=> ∃ x, α x ∗ (∀ y, β x y -∗ |={Ei, Eo}=> Ψ x y))

/-- **Open a one-shot update and commit.** `wpi_aupd_commit` for the one-shot -/
theorem wpi_oneShot_commit {A B : Type _} (t : ITree Eff V)
    (α : A → IProp GF) (β Ψ : A → B → IProp GF) (Φ : Post GF V) :
    oneShotUpd ⊤ ∅ α β Ψ ⊢
      iprop((∀ x, α x -∗ wpi_mask GF Hd m t (fun v => iprop(∃ y, β x y ∗ (Ψ x y -∗ Φ v))) ∅) -∗
            wpi_mask GF Hd m t Φ ⊤) := by
  simp only [oneShotUpd]
  iintro HOS Hbody
  iapply (AeneasIris.wpi_clear_mask (H := Hd) t Φ ⊤).mp
  imod HOS with ⟨%x, Hα, Hcommit⟩
  imodintro
  iapply (AeneasIris.wpi_wand (H := Hd) t
            (fun v => iprop(∃ y, β x y ∗ (Ψ x y -∗ Φ v)))
            (fun v => iprop(|={∅, ⊤}=> Φ v)) ∅) $$ [Hcommit]
  · iintro %v ⟨%y, Hβ, Hret⟩
    imod Hcommit $$ Hβ with HΨ
    imodintro
    iapply Hret $$ HΨ
  · iapply Hbody $$ Hα

/-- **A plain spec implies the one-shot spec, and not conversely.** -/
theorem wpi_oneShot_of_plain (t : ITree Eff V) (A : IProp GF) (Φ : Post GF V) :
    iprop(A -∗ wpi_mask GF Hd m t Φ ∅) ⊢
      iprop(oneShotUpd ⊤ ∅ (fun _ : Unit => A) (fun _ _ : Unit => iprop(True))
              (fun _ _ => iprop(True)) -∗ wpi_mask GF Hd m t Φ ⊤) := by
  iintro Hplain HOS
  iapply (wpi_oneShot_commit (Hd := Hd) t _ _ _ Φ) $$ HOS
  iintro %x HA
  iapply (AeneasIris.wpi_wand (H := Hd) t Φ
            (fun v => iprop(∃ _y : Unit, True ∗ (True -∗ Φ v))) ∅) $$ []
  · iintro %v HΦ
    iexists ()
    isplitl []
    · itrivial
    · iintro _
      iexact HΦ
  · iapply Hplain $$ HA

end OneShot

end

end AeneasIris.AtomicWpi
