import AeneasIris.Tactics.ISpec
import AeneasIris.Effects.Step

/-! # Triples -/

namespace AeneasIris

open Iris BI Aeneas.Data.Coinductive
open AeneasIris.Step (lat)
open Aeneas.Std (Result RustEffect)

unseal Aeneas.Std.Result

universe u

section

variable {hlc : Iris.HasLC} {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]

/-! ## Notation -/

syntax:40 "⦃" term "⦄ " term:max " @ " term:max " ; " term:max " ; " term:max
          " ⦃" ident ", " term "⦄" : term

macro_rules
  | `(⦃$P⦄ $t @ $H ; $m ; $M ⦃$v, $Q⦄) =>
    `(iprop($P) ⊢ AeneasIris.wpi_mask _ $H $m $t (fun $v => iprop($Q)) $M)

/-! ## The `apply` lemmas -/

/-- `iSpec`, curried for `iapply … $$ [$]`. -/
theorem iSpec.apply {E : Effect} {α : Type} {H : Handler E GF} {m : Mode} {P : IProp GF}
    {t : ITree E α} {Q : Post GF α} {M : CoPset}
    (h : iSpec H m P t Q M) (Φ : Post GF α) :
    P ⊢ iprop((∀ v, Q v -∗ Φ v) -∗ wpi_mask GF H m t Φ M) := by
  iintro HP Hk
  iapply (wpi_wand (H := H) t Q Φ M) $$ Hk
  iapply (BI.entails_wand h)
  iexact HP

/-! ## Peeling the step -/

section Step

open AeneasIris.Step (stepP stepH)
open Aeneas.Std (StepE)

variable {hlc : Iris.HasLC} {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF]
variable {E : Effect} [StepE -< E]
variable {Hd : Handler E GF} {m : Mode} [stepH GF m -<ₕ Hd]

/-- `Step.wpi_stepThen` at `P := wpi_mask … (k ()) Φ M`. -/
theorem wpi_stepThen' {α : Type v} (k : PUnit.{v+1} → ITree E α) (Φ : Post GF α)
    (M : CoPset) :
    lat m (wpi_mask GF Hd m (k PUnit.unit) Φ M)
      ⊢ wpi_mask GF Hd m (ITree.bind stepP.{v, _} k) Φ M :=
  Step.wpi_stepThen (k PUnit.unit) Φ M .rfl

/-- The step as an ordinary Hoare triple: `∀ P, ⦃ lat m P ⦄ stepP ⦃ _, P ⦄`. -/
theorem step_spec (P : IProp GF) (M : CoPset) :
    ⦃ lat m P ⦄ (stepP.{0, _} (E := E)) @ Hd ; m ; M ⦃ _r, P ⦄ :=
  .trans (Step.lat_mono' m Iris.fupd_intro)
    (Step.wpi_stepP (m := m) (Hd := Hd) (fun _ => P) M)

/-- `wpi_stepThen'` *is* `step_spec`, continuationised — derived here rather than asserted. -/
theorem wpi_stepThen'_from_step_spec {α : Type} (k : PUnit.{1} → ITree E α)
    (Φ : Post GF α) (M : CoPset) :
    lat m (wpi_mask GF Hd m (k PUnit.unit) Φ M)
      ⊢ wpi_mask GF Hd m (ITree.bind stepP.{0, _} k) Φ M := by
  refine .trans ?_ (wpi_bind (H := Hd) stepP.{0, _} k Φ M)
  iintro Hlat
  iapply (iSpec.apply (H := Hd)
      (step_spec (m := m) (E := E) (Hd := Hd) (wpi_mask GF Hd m (k PUnit.unit) Φ M) M)
      (fun v => wpi_mask GF Hd m (k v) Φ M)) $$ [Hlat]
  · iexact Hlat
  ·
    iintro %v Hp
    iexact Hp

end Step

/-! ## The registry -/

namespace IStep

open Lean

/-- Which style a rule is stated in, which is what decides how `irule` applies it. -/
inductive Style where
  /-- `⦃P⦄ t ⦃v, Q⦄`. -/
  | triple
  /-- Already continuation-style: the premise mentions the weakest precondition of the continuation. -/
  | cont
  /-- An `IASpec`: the ordinary precondition is framed, the update becomes a goal. -/
  | atomic
deriving Inhabited, Repr, DecidableEq

structure Info where
  /-- The tagged theorem. -/
  rule : Name
  /-- How many explicit arguments the rule takes before its conclusion. -/
  nExplicit : Nat
  /-- Which style it is stated in. -/
  style : Style := .triple
  /-- Does it take a `Mode`? -/
  mintsLat : Bool := false
deriving Inhabited, Repr

/-- The leading operation of a bind, or `none` in tail position. -/
def headOp? (prog : Expr) : Option Expr :=
  let (f, args) := prog.consumeMData.withApp (fun f args => (f, args))
  if f.isConstOf ``bind ∧ args.size = 6 then some args[4]!
  else if f.isConstOf ``_root_.Aeneas.Std.bind ∧ args.size = 4 then some args[2]!
  else if f.isConstOf ``Aeneas.Data.Coinductive.ITree.bind ∧ args.size = 5 then
    some args[3]!
  else none

/-- Several rules may be registered for one operation — `cas` has one for the -/
initialize ext : SimplePersistentEnvExtension (Name × Info) (NameMap (Array Info)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (op, i) => m.insert op ((m.find? op |>.getD #[]).push i)
    addImportedFn := fun arrs =>
      arrs.foldl (fun m a =>
        a.foldl (fun m (op, i) => m.insert op ((m.find? op |>.getD #[]).push i)) m) {}
  }

/-- The rules registered for an operation, in registration order. -/
def find? (env : Environment) (op : Name) : Array Info :=
  (ext.getState env).find? op |>.getD #[]

open Meta in
/-- Read `(operation, explicit-argument count)` off a rule's conclusion. -/
def analyse (decl : Name) (style : Style) : MetaM (Name × Nat × Bool) := do
  forallTelescope (← getConstInfo decl).type fun xs body => do
    /- Where the program sits depends on the shape concluded in: an entailment
    into `wpi_mask` and an `iSpec` both end `… t Φ M`, whereas an `IASpec` ends
    `… t E α β POST f`.  `IASpec` is named rather than referenced so that this
    file need not import it. -/
    let (carrier, back) ←
      if body.isAppOfArity ``Iris.BI.BIBase.Entails 4 then pure (body.appArg!, 3)
      else if body.getAppFn.isConstOf ``AeneasIris.iSpec then pure (body, 3)
      else if body.getAppFn.constName? == some `AeneasIris.OneShotWpi.IASpec then
        pure (body, 6)
      else throwError
        "istep_rule: {decl} concludes in {body.getAppFn}, not in `iSpec`, `IASpec` \
         or an entailment into `wpi_mask`"
    let args := carrier.getAppArgs
    if args.size < back + 1 then
      throwError "istep_rule: {decl}'s conclusion is applied to too few arguments"
    let prog := args[args.size - back]!
    let keyed := if style == .cont then (headOp? prog).getD prog else prog
    let some op := keyed.getAppFn.constName?
      | throwError "istep_rule: {decl}'s program is not headed by a constant"
    /- Whether the rule mints a `▷` is a property of its *precondition*, not of
    its argument list: a rule can take a `Mode` and still demand an ordinary
    resource (`sync_spec`) or a plain one (`load_na_spec`).  Deciding it by
    scanning for a `Mode`-typed argument made `applyCont` append a `lat`
    introduction that such a rule cannot discharge, so the rule failed and
    `istep` fell through. -/
    let pre :=
      if body.isAppOfArity ``Iris.BI.BIBase.Entails 4 then body.appFn!.appArg!
      else args[args.size - 4]!
    let mintsLat := pre.consumeMData.getAppFn.isConstOf ``AeneasIris.Step.lat
    let mut n := 0
    for x in xs do
      let d ← x.fvarId!.getDecl
      if d.binderInfo.isExplicit then n := n + 1
    return (op, n, mintsLat)

open Meta in
/-- The attribute's body. -/
def addRule (decl : Name) (stx : Syntax) (kind : AttributeKind) : AttrM Unit := do
  unless kind == AttributeKind.global do
    throwError "istep_rule: only global registration is supported"
  let style : Style :=
    if stx[1].isNone then .triple
    else if stx[1][0].isOfKind `token.atomic || stx[1][0].getAtomVal == "atomic" then .atomic
    else .cont
  let (op, n, mintsLat) ← MetaM.run' (analyse decl style)
  modifyEnv (ext.addEntry · (op, { rule := decl, nExplicit := n, style, mintsLat }))

/-- `@[istep_rule]` / `@[istep_rule cont]` / `@[istep_rule atomic]`. -/
syntax (name := istep_rule) "istep_rule" (ppSpace (&"cont" <|> &"atomic"))? : attr

initialize registerBuiltinAttribute {
    name := `istep_rule
    descr := "spec rule for `istep`, indexed by the operation it is about"
    add := fun decl stx kind => addRule decl stx kind
  }

end IStep

end

end AeneasIris
