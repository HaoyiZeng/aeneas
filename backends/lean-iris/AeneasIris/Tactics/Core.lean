import AeneasIris.Tactics.ISpec
import AeneasIris.Rust
import AeneasIris.Tactics.Triple
import Iris.BI.WeakestPre

/-! # Tactics -/

namespace AeneasIris

open Iris BI Aeneas.Data.Coinductive
open Aeneas.Std (Result RustEffect)

attribute [istep_rule cont] wpi_stepThen'

unseal Aeneas.Std.Result

/-- `wpi_bind` stated with `Result`'s own bind. -/
theorem wpi_bind_result {hlc : Iris.HasLC} {GF : BundledGFunctors}
    [Iris.InvGS_gen hlc GF] {α β : Type} {H : Handler RustEffect GF}
    (t : Result α) (k : α → Result β) (Φ : Post GF β) (M : CoPset) :
    wpi_mask GF H m t (fun v => wpi_mask GF H m (k v) Φ M) M
      ⊢ wpi_mask GF H m (Aeneas.Std.bind t k) Φ M :=
  wpi_bind (H := H) t k Φ M

/-- `wpi_ret` stated with `Result.ok`, for the same reason as -/
theorem wpi_ret_result {hlc : Iris.HasLC} {GF : BundledGFunctors}
    [Iris.InvGS_gen hlc GF] {α : Type} {H : Handler RustEffect GF}
    (v : α) (Φ : Post GF α) (M : CoPset) :
    Φ v ⊢ wpi_mask GF H m (Result.ok v) Φ M :=
  wpi_ret (H := H) v Φ M

/-- Hand a returned value to the postcondition. -/
macro "iret" : tactic =>
  `(tactic|
    (first | simp only [reduceIte, Bool.false_eq_true, eq_self_iff_true,
                        if_true, if_false] | skip
     first
     | iapply (wpi_ret_result _ _ _)
     | iapply (AeneasIris.wpi_ret _ _ _)))

/-- The core of `istep`, without the context bookkeeping. -/
macro "istep_core" args:Aeneas.Step.stepArgs : tactic =>
  `(tactic| ((first | refine iSpec_intro ?_ | show iSpec _ _ _ _ _);
             step $args))

/-! ## The step tactics, declared ahead of use -/

/-- Apply the rule registered for the leading operation. -/
syntax "irule" (" with " ident)? (" as " (colGt ppSpace introPat)*)? : tactic

open Lean in
/-- The first identifier anywhere in a pattern. -/
partial def firstIdent? (s : Syntax) : Option Syntax :=
  if s.isIdent then some s else s.getArgs.findSome? firstIdent?

open Lean in
/-- Does this pattern destructure rather than name? Recognised by its bracket -/
partial def isTuplePat (s : Syntax) : Bool :=
  s.getArgs.any (fun a => (a.getAtomVal == "⟨") || isTuplePat a)

open Lean Elab Tactic Meta in
/-- Translate an intro pattern into an `rcases` one. -/
partial def icasesToRcases (s : Syntax) : TacticM (TSyntax `rcasesPat) := do
  if s.isIdent then return ← `(rcasesPat| $(⟨s⟩):ident)
  for a in s.getArgs do
    if a.getAtomVal == "⟨" then
      let elems := s.getArgs[1]!.getSepArgs
      let subs ← elems.mapM (fun e => icasesToRcases e)
      return ← `(rcasesPat| ⟨$subs,*⟩)
  match s.getArgs.filter (fun a => !a.isAtom) with
  | #[c] => icasesToRcases c
  | _ => `(rcasesPat| _)

/-- The `as` clause of `istep`: `step`'s, widened to full `rcases` patterns. -/
syntax istepArgs := Lean.Parser.Tactic.optConfig (" with " term)?
                    (" as " " ⟨ " introPat,* " ⟩")? (" by " tacticSeq)?

open Lean Elab Tactic Meta in
/-- Consume a leading *pure* Aeneas call, keeping the proof-mode context. -/
elab "istep" args:istepArgs : tactic => do
  let `(istepArgs| $_ $[with $_]? $[as ⟨ $pats,* ⟩]? $[by $_]?) := args
    | throwError "istep: could not read the arguments"
  let mut ids : Array Syntax := #[]
  let mut unpack : Array (Name × TSyntax `introPat) := #[]
  let asBinderIdent (stx : Syntax) : TacticM Syntax := do
    let some id := firstIdent? stx
      | return (← `(Lean.binderIdent| _)).raw
    return (← `(Lean.binderIdent| $(⟨id⟩):ident)).raw
  for p in (pats.map (·.getElems)).getD #[] do
    if isTuplePat p.raw then
      let nm := Name.mkSimple s!"istepPacked{unpack.size}"
      ids := ids.push (← asBinderIdent (mkIdent nm))
      unpack := unpack.push (nm, p)
    else
      ids := ids.push (← asBinderIdent p.raw)
  let raw := args.raw
  let raw :=
    if raw[2].getNumArgs == 0 then raw
    else
      let grp := raw[2]
      let sep := grp[2].setArgs <| grp[2].getArgs.mapIdx fun i a =>
        if i % 2 == 0 then ids[i / 2]! else a
      raw.setArg 2 (grp.setArg 2 sep)
  let stepArgs : TSyntax ``Aeneas.Step.stepArgs :=
    ⟨raw.setKind ``Aeneas.Step.stepArgs⟩
  let saved ← do
    let ty ← instantiateMVars (← (← getMainGoal).getType)
    if ty.isAppOfArity ``Iris.ProofMode.Entails' 4 then pure (some ty) else pure none
  let heapPats : Array (TSyntax `introPat) := (pats.map (·.getElems)).getD #[]
  let ruleAlt ← if heapPats.isEmpty then `(tactic| irule)
                else `(tactic| irule as $heapPats*)
  let mut usedRule := false
  let mut ruleErr : Option MessageData := none
  try
    evalTactic (← `(tactic| $ruleAlt:tactic))
    usedRule := true
  catch e => ruleErr := some e.toMessageData
  if usedRule then return
  let mut usedRet := false
  try
    evalTactic (← `(tactic| iret))
    usedRet := true
  catch _ => pure ()
  if usedRet then return
  if let some re := ruleErr then
    /- `irule` reports "is not a `wpi_mask`" both when the goal really is one and
    the reified context has gone stale, and when the goal is simply another
    entailment.  Throwing is load-bearing in *both* cases -- falling through lets
    `istep` consume the goal and leave a `sorryAx` -- so only the diagnosis is
    chosen here, never whether to complain. -/
    if ((← re.toString).splitOn "is not a `wpi_mask`").length > 1 then
      let tyRaw ← match saved with
        | some ty => pure ty
        | none => do
            let g ← getMainGoal
            instantiateMVars (← g.getType)
      /- `consumeMData` first: a goal carrying metadata fails `isAppOfArity`, which
      is why `saved` is `none` here even for an `Entails'`.  Read the target
      through `Entails'` or plain `Entails` before classifying it. -/
      let ty := tyRaw.consumeMData
      let tgt := (if ty.isAppOfArity ``Iris.ProofMode.Entails' 4
                     || ty.isAppOfArity ``Iris.BI.BIBase.Entails 4 then ty.appArg!
                  else ty).consumeMData
      if tgt.isAppOf ``AeneasIris.wpi_mask || tgt.isAppOf ``AeneasIris.iSpec then
        throwError "istep: the goal is a `wpi_mask`, but `irule` could not read it, so no rule fired.\n\nirule said:\n{re}\n\nUsually this means the reified proof-mode context went stale: a `have`, `rcases`, `cases`, `split` or `rw` between proof-mode steps rebuilds the goal and invalidates it, even though the goal still prints correctly. If there is such a step above, hoist it above the opening `iintro`, or destructure inside the proof-mode tactic instead (e.g. `iintro ⟨a, b⟩`); `simp only` is safe.\n\nIf there is no such step, do not go looking for one — this message reports what `irule` could not do, not why."
      else
        throwError "istep: the goal is not a `wpi_mask`, so no step rule applies.\n\n`istep` expects `⦃P⦄ t ⦃v, Q⦄` or an entailment into `wpi_mask`. This goal is an ordinary entailment (a wand, `emp -∗ <wp>`, or similar), which is proof-mode work: use `iintro`, `iexact`, `isplit`, `iapply` and friends.\n\nIf you did expect a `wpi_mask`, `iintro` the wand first -- `ihave … $$ …` leaves exactly this shape behind."
  try
    evalTactic (← `(tactic| istep_core $stepArgs))
  catch e =>
    try
      evalTactic (← `(tactic| iret))
    catch _ =>
      match ruleErr with
      | none => throw e
      | some re =>
        throwError "istep: no registered rule applied, and the pure fallback failed too.\n\n          irule said:\n{re}\n\n          istep_core said:\n{e.toMessageData}\n\n          If irule says the goal is not a `wpi_mask` while it prints as one, the reified           proof-mode context was invalidated by a `have`, `rcases`, `cases`, `split` or           `rw` earlier in the block. Hoist it above the opening `iintro`, or destructure           inside the proof-mode tactic instead. `simp only` is safe."
    return
  let some origTy := saved | return
  let mkPM := origTy.appFn!.appFn!
  let gs ← getUnsolvedGoals
  let mut gs' := #[]
  for g in gs do
    let ty ← g.withContext do instantiateMVars (← g.getType)
    if ty.isAppOfArity ``Iris.BI.BIBase.Entails 4 then
      let ty' := (mkPM.app ty.appFn!.appArg!).app ty.appArg!
      gs' := gs'.push (← g.replaceTargetDefEq ty')
    else
      gs' := gs'.push g
  replaceMainGoal gs'.toList
  for (nm, pat) in unpack do
    let g ← getMainGoal
    let some found ← g.withContext do
        pure <| (← getLCtx).findDecl? fun d =>
          if !d.isImplementationDetail && d.userName.eraseMacroScopes == nm then
            some d.userName
          else none
      | throwError "istep: the result `{nm}` to unpack is not in the context"
    let rpat ← icasesToRcases pat.raw
    evalTactic (← `(tactic| obtain $rpat := $(mkIdent found)))

/-! ## Notation -/

/-- The `A` slot carries the handler **and** the mode, because together they are -/
instance {hlc : Iris.HasLC} {GF : BundledGFunctors} [Iris.InvGS_gen hlc GF] {α : Type} :
    Iris.Wp (IProp GF) (Result α) α (Handler RustEffect GF × Mode) where
  wp Hm M t Φ := wpi_mask GF Hm.1 Hm.2 t Φ M

/-- Normalise the `lat` wrapper away. -/
macro "ilat" : tactic =>
  `(tactic| simp only [AeneasIris.Step.lat_identity, AeneasIris.Step.lat_later])

/-! ## Reading the goal -/

namespace Read

open Lean Meta

/-- The four fields of a `wpi_mask` goal that a tactic needs. -/
structure WpGoal where
  handler : Expr
  /-- The `Mode` the weakest precondition is read at. -/
  mode    : Expr
  program : Expr
  post    : Expr
  mask    : Expr

/-- Read a `wpi_mask` application. -/
def wpGoal? (e : Expr) : Option WpGoal := do
  let (f, args) := e.consumeMData.getAppFnArgs
  let n := args.size
  match f with
  | ``AeneasIris.wpi_mask =>
    if n ≥ 5 then
      some { handler := args[n - 5]!, mode    := args[n - 4]!
             program := args[n - 3]!, post    := args[n - 2]!
             mask    := args[n - 1]! }
    else none
  | ``Iris.Wp.wp =>
    if n ≥ 4 then
      let hm := args[n - 4]!
      some { handler := mkProj ``Prod 0 hm, mode := mkProj ``Prod 1 hm
             mask    := args[n - 3]!
             program := args[n - 2]!, post    := args[n - 1]! }
    else none
  | _ => none

/-- Strip the proof-mode wrapper, if any, and read the `wpi_mask` underneath. -/
def ofGoalTy? (ty : Expr) : Option WpGoal :=
  let rhs :=
    if ty.isAppOfArity ``Iris.ProofMode.Entails' 4 then ty.appArg!
    else if ty.isAppOfArity ``Iris.BI.BIBase.Entails 4 then ty.appArg!
    else ty
  wpGoal? rhs

/-- Reduce leading pattern-matches, and nothing else, to expose a bind. -/
partial def exposeBind (headOp? : Expr → Option Expr) (e : Expr) :
    Nat → MetaM (Option (Expr × Expr))
  | 0 => return none
  | fuel + 1 => do
    if let some h := headOp? e then return some (e, h)
    let e' ← whnfCore e
    if let some h := headOp? e' then return some (e', h)
    if e'.consumeMData.isAppOf ``Aeneas.Std.uncurry then
      if let some u ← unfoldDefinition? e' then
        return ← exposeBind headOp? u fuel
    return none

/-- Put a program back into a `wpi_mask` application. -/
def setProgram (e : Expr) (prog : Expr) : Option Expr :=
  e.consumeMData.withApp fun f args =>
    let n := args.size
    if n < 4 then none
    else if f.isConstOf ``AeneasIris.wpi_mask then some (mkAppN f (args.set! (n - 3) prog))
    else if f.isConstOf ``Iris.Wp.wp then some (mkAppN f (args.set! (n - 2) prog))
    else none

/-- Put a program back into a goal, through the proof-mode wrapper if there is one. -/
def setProgramInGoal (ty : Expr) (prog : Expr) : Option Expr :=
  if ty.isAppOfArity ``Iris.ProofMode.Entails' 4
      || ty.isAppOfArity ``Iris.BI.BIBase.Entails 4 then
    (setProgram ty.appArg! prog).map (fun rhs => ty.appFn!.app rhs)
  else setProgram ty prog

/-- The leading operation of a `do` block, or `none` in tail position. -/
def headOp? : Expr → Option Expr := IStep.headOp?

/-- Every named hypothesis of a reified proof-mode context. -/
partial def collectHyps (e : Expr) (acc : Array (Name × Expr) := #[]) :
    Array (Name × Expr) :=
  match Iris.ProofMode.parseName? e with
  | some (name, _, ty) => acc.push (name, ty)
  | none =>
    if e.isAppOfArity ``Iris.BI.BIBase.sep 4 then
      collectHyps e.appArg! (collectHyps e.appFn!.appArg! acc)
    else acc

end Read

open Lean Elab Tactic Meta in
/-- Expose the leading operation of a `do` block. -/
elab "ibind" op:(ppSpace colGt term)? : tactic => do
  let bindAt : TSyntax `term → TacticM Unit := fun o => do
    let tac ← `(tactic|
      first
      | iapply (wpi_bind_result $o _ _ _)
      | iapply (wpi_bind $o _ _ _))
    evalTactic tac
  match op with
  | some op => bindAt op
  | none =>
    evalTactic (← `(tactic|
      (first | simp only [Aeneas.Std.bind_assoc_eq, bind_assoc_eq] | skip)))
    let g ← getMainGoal
    let ty ← g.withContext do instantiateMVars (← g.getType)
    let some wp := Read.ofGoalTy? ty
      | throwError "ibind: goal is not a `wpi_mask`{indentExpr ty}"
    let some (prog, head) ← g.withContext do Read.exposeBind Read.headOp? wp.program 8
      | return
    let g ← if prog == wp.program then pure g else
      match Read.setProgramInGoal ty prog with
      | some ty' => g.replaceTargetDefEq ty'
      | none => pure g
    replaceMainGoal [g]
    let headStx ← g.withContext do Term.exprToSyntax head
    bindAt headStx

/-! ## Applying a registered rule -/

namespace Read

open Lean Meta

/-- The operation the goal begins with, in either position. -/
def goalOp? (ty : Expr) : MetaM (Option Expr) := do
  let some wp := ofGoalTy? ty | return none
  match ← exposeBind headOp? wp.program 8 with
  | some (_, h) => return some h
  | none => return some wp.program

/-- Heads that build a *returned value* rather than an operation. -/
def valueFormer (c : Name) : Bool :=
  if c == ``ITree.ret then true
  else if c == ``Pure.pure then true
  else c == ``Aeneas.Std.Result.ok

/-- δ-unfold an operation until its head is one the registry knows. -/
partial def knownBody? (e : Expr) : Nat → MetaM (Option Expr)
  | 0 => return none
  | fuel + 1 => do
    let e' ← whnfCore e.consumeMData
    match headOp? e' with
    | some hd =>
      if let some c := hd.consumeMData.getAppFn.constName? then
        if !(IStep.find? (← getEnv) c).isEmpty then return some e'
      return none
    | none =>
      if let some c := e'.consumeMData.getAppFn.constName? then
        if !(IStep.find? (← getEnv) c).isEmpty then return some e'
        if valueFormer c then return none
      if let some u ← unfoldDefinition? e' then knownBody? u fuel else return none

/-- Reduce the goal's program, without δ. -/
def normProgramInGoal (g : MVarId) : MetaM (Option MVarId) := do
  let ty ← g.withContext do instantiateMVars (← g.getType)
  let some wp := ofGoalTy? ty | return none
  let prog ← g.withContext do whnfCore wp.program
  if prog == wp.program then return none
  let some ty' := setProgramInGoal ty prog | return none
  return some (← g.replaceTargetDefEq ty')

/-- Split a `∗`-chain into its components. -/
partial def sepComponents (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  let e' := e.consumeMData
  if e'.isAppOfArity ``Iris.BI.BIBase.sep 4 then
    sepComponents e'.appArg! (sepComponents e'.appFn!.appArg! acc)
  else acc.push e'

/-- The head symbols of the resources a rule's precondition asks for. -/
def ruleResourceHeads (rule : Name) : MetaM (Array Name) := do
  forallTelescope (← getConstInfo rule).type fun _ body => do
    let pre ←
      if body.isAppOfArity ``Iris.BI.BIBase.Entails 4 then pure body.appFn!.appArg!
      else if body.getAppFn.isConstOf ``AeneasIris.iSpec then
        let args := body.getAppArgs
        if args.size < 4 then return #[] else pure args[args.size - 4]!
      else return #[]
    return (sepComponents pre).filterMap (·.consumeMData.getAppFn.constName?)

/-- Is this component a pure proposition `⌜φ⌝`? -/
def isPure (e : Expr) : Bool := e.consumeMData.isAppOf ``Iris.BI.BIBase.pure

/-- The named hypotheses of the current proof-mode context, in order. -/
def ctxNames (ty : Expr) : Array Name :=
  let ctx :=
    if ty.isAppOfArity ``Iris.ProofMode.Entails' 4 then ty.appFn!.appArg! else ty
  (collectHyps ctx).map (·.1)

end Read

open Lean Elab Tactic Meta in
/-- Apply the rule registered for the goal's leading operation. -/
elab_rules : tactic
  | `(tactic| irule $[with $ruleName?]? $[as $pats*]?) => do
  let userPats : Array (TSyntax `introPat) := pats.getD #[]
  let discharge : TacticM Unit := do
    let gs ← getUnsolvedGoals
    let mut rest := #[]
    for gi in gs do
      let ty ← gi.withContext do instantiateMVars (← gi.getType)
      if (← gi.withContext do isClass? ty).isSome then
        try
          gi.assign (← gi.withContext do synthInstance ty)
        catch _ => rest := rest.push gi
      else rest := rest.push gi
    replaceMainGoal rest.toList
  let readOp : TacticM (Expr × Name × Expr) := do
    let g ← getMainGoal
    let ty ← g.withContext do instantiateMVars (← g.getType)
    let some op ← g.withContext do Read.goalOp? ty
      | throwError "irule: the goal is not a `wpi_mask`"
    let some c := op.getAppFn.constName?
      | throwError "irule: the operation {op} is not headed by a constant"
    return (ty, c, op)
  let applyCont : IStep.Info → TacticM Unit := fun info => do
    let rule := mkIdent info.rule
    let g₀ ← getMainGoal
    let mut alts : Array (TSyntax `tactic) := #[]
    let ty₀ ← g₀.withContext do instantiateMVars (← g₀.getType)
    match (Read.ofGoalTy? ty₀).map (·.mode) with
    | some mExpr =>
      /- The goal carries the `Mode`, so read it instead of enumerating the
      `Mode`-typed locals and trying each.  Reading also works when the mode is
      not a local at all (a section variable or a metavariable), which the
      enumeration could only fail on, and a genuine failure now reports itself
      rather than whatever the last guess happened to say. -/
      let mStx ← g₀.withContext do Term.exprToSyntax mExpr
      let mWhnf ← g₀.withContext do whnf mExpr
      let latTac : TSyntax `tactic ←
        if mWhnf.isConstOf ``AeneasIris.Mode.total then `(tactic| ilat)
        else if mWhnf.isConstOf ``AeneasIris.Mode.part then `(tactic| (ilat; inext))
        else `(tactic| iapply AeneasIris.Step.lat_intro)
      alts := #[← `(tactic| (iapply ($rule (m := $mStx)); $latTac))]
    | none =>
      let locals ← g₀.withContext do
        let mut acc : Array Term := #[]
        for d in ← getLCtx do
          if !d.isImplementationDetail then
            if (← instantiateMVars d.type).isConstOf
                ``AeneasIris.Mode then
              acc := acc.push (mkIdent d.userName)
        pure acc
      for mt in locals do
        alts := alts.push (← `(tactic|
          (iapply ($rule (m := $mt)); iapply AeneasIris.Step.lat_intro)))
      alts := alts.push (← `(tactic|
        (iapply ($rule (m := AeneasIris.Mode.part)); ilat; inext)))
      alts := alts.push (← `(tactic|
        (iapply ($rule (m := AeneasIris.Mode.total)); ilat)))
    unless info.mintsLat do alts := #[← `(tactic| iapply ($rule))]
    evalTactic (← `(tactic| first $[| $alts:tactic]*))
    if let some g' ← (← getMainGoal).withContext do
        Read.normProgramInGoal (← getMainGoal) then
      replaceMainGoal [g']
  let mut found : Option (Expr × Name × Expr) := none
  /- An `IASpec` is applied through `IASpec.wand`, which is its entailment form:
  the ordinary precondition is framed out of the context -- `itrivial` covers the
  usual `emp` -- and the update is left as a goal for the caller, who is the one
  that knows whether the resource is owned or shared. -/
  let applyAtomic : IStep.Info → TacticM Unit := fun info => do
    let rule := mkIdent info.rule
    let wand := mkIdent `AeneasIris.OneShotWpi.IASpec.wand
    let holes : Array Term := Array.replicate info.nExplicit (← `(_))
    let ctx ← do
      let ty ← instantiateMVars (← (← getMainGoal).getType)
      pure (Read.ctxNames ty)
    let mut alts : Array (TSyntax `tactic) := #[]
    for n in ctx do
      let nId := mkIdent n
      alts := alts.push (← `(tactic| iapply ($wand ($rule $holes*) _) $$ [$nId:ident]))
    alts := alts.push (← `(tactic| (iapply ($wand ($rule $holes*) _) $$ []; itrivial)))
    evalTactic (← `(tactic| first $[| $alts:tactic]*))
  let mut stepped := false
  let mut stuck : Name := .anonymous
  for _ in [0:8] do
    let (_, c₁, _) ← readOp
    if let some info := (IStep.find? (← getEnv) c₁).find? (·.style == .cont) then
      applyCont info
      stepped := true
    else
      evalTactic (← `(tactic| ibind))
      let (ty₂, c₂, op₂) ← readOp
      if (IStep.find? (← getEnv) c₂).any (·.style == .triple) then
        found := some (ty₂, c₂, op₂)
        break
      stuck := c₂
      match ← (← getMainGoal).withContext do Read.knownBody? op₂ 8 with
      | none => break
      | some exposed =>
        let g ← getMainGoal
        match Read.setProgramInGoal ty₂ exposed with
        | none => break
        | some ty' => replaceMainGoal [← g.replaceTargetDefEq ty']
  if found.isNone then
    if stepped then return
    throwError "irule: no rule is registered for {stuck}"
  let (ty0, c, op) := found.get!
  let infos ← match ruleName? with
    | some r =>
      let n ← realizeGlobalConstNoOverloadWithInfo r
      let (_, nExp, _) ← MetaM.run' (IStep.analyse n .triple)
      pure #[({ rule := n, nExplicit := nExp, style := .triple, mintsLat := false }
              : IStep.Info)]
    | none => pure ((IStep.find? (← getEnv) c).filter (·.style == .triple))
  if infos.isEmpty then
    /- No sequential rule, but perhaps an atomic one: a shared resource cannot be
    framed out of the context, so the triple path could not have applied. -/
    if let some info := (IStep.find? (← getEnv) c).find? (·.style == .atomic) then
      applyAtomic info
      return
    throwError "irule: no rule is registered for {c}"
  let applyThm := mkIdent ``AeneasIris.iSpec.apply
  let before := Read.ctxNames ty0
  let g' ← getMainGoal
  let opStx ← g'.withContext do
    let ty ← instantiateMVars (← g'.getType)
    match ← Read.goalOp? ty with
    | some o => Term.exprToSyntax o
    | none   => Term.exprToSyntax op
  let ctxHyps :=
    let ctx :=
      if ty0.isAppOfArity ``Iris.ProofMode.Entails' 4 then ty0.appFn!.appArg! else ty0
    Read.collectHyps ctx
  let mkAlt : IStep.Info → TSyntax `specPat → TacticM (TSyntax `tactic) :=
    fun info pat => do
      let ruleId := mkIdent info.rule
      let holes : Array Term := Array.replicate info.nExplicit (← `(_))
      `(tactic| iapply ($applyThm (t := $opStx) ($ruleId $holes*) _) $$ $pat)
  let mut ruleAlts : Array (TSyntax `tactic) := #[]
  for info in infos do
    let heads ← try g'.withContext do Read.ruleResourceHeads info.rule
                catch _ => pure #[]
    for (n, t) in ctxHyps do
      if let some c := t.consumeMData.getAppFn.constName? then
        if heads.contains c then
          let nId := mkIdent n
          let payer ← `(frameIdent| $nId:ident)
          let app ← mkAlt info (← `(specPat| [$payer]))
          ruleAlts := ruleAlts.push (← `(tactic| ($app; iexact $nId)))
  for info in infos do
    ruleAlts := ruleAlts.push (← mkAlt info (← `(specPat| [$])))
  for info in infos do
    ruleAlts := ruleAlts.push (← mkAlt info (← `(specPat| [//])))
  /- A `cont` rule may already have consumed an operation, exposing a next one
  whose resources are not available yet -- they can still be inside an atomic
  update the caller has to commit first.  Failing here would throw that progress
  away and report the *second* operation, so keep what was stepped and let the
  caller carry on. -/
  if stepped then
    try evalTactic (← `(tactic| first $[| $ruleAlts:tactic]*))
    catch _ => return
  else
    try evalTactic (← `(tactic| first $[| $ruleAlts:tactic]*))
    catch e =>
      /- The sequential rules all wanted to frame a resource out of the context.
      A shared one is not there to be framed, so try the atomic rule, which asks
      for an update instead. -/
      if let some info := (IStep.find? (← getEnv) c).find? (·.style == .atomic) then
        applyAtomic info
        return
      throw e
  discharge
  do
    let gs ← getUnsolvedGoals
    let mut pm : Array MVarId := #[]
    let mut rest : Array MVarId := #[]
    for gi in gs do
      let ty ← gi.withContext do instantiateMVars (← gi.getType)
      if ty.isAppOfArity ``Iris.ProofMode.Entails' 4 then pm := pm.push gi
      else rest := rest.push gi
    unless pm.isEmpty do replaceMainGoal (pm.toList ++ rest.toList)
  let g₁ ← getMainGoal
  let ty₁ ← g₁.withContext do instantiateMVars (← g₁.getType)
  let after := Read.ctxNames ty₁
  let consumed := before.filter (fun n => !after.contains n)
  let mut fresh := 0
  let mkFresh : Nat → Ident := fun i => mkIdent (Name.mkSimple s!"iruleRes{i}")
  let mkPure (id : Ident) : TacticM (TSyntax `icasesPat) := do
    let b ← `(Lean.binderIdent| $id:ident)
    `(icasesPat| %$b:binderIdent)
  let mkNamed (id : Ident) : TacticM (TSyntax `icasesPat) := do
    let b ← `(Lean.binderIdent| $id:ident)
    `(icasesPat| $b:binderIdent)
  let valPat : TSyntax `icasesPat ←
    match userPats[0]? >>= (firstIdent? ·.raw) with
    | some id => mkPure ⟨id⟩
    | none    => do
      let b ← `(Lean.binderIdent| _)
      `(icasesPat| %$b:binderIdent)
  let valIntro ← `(introPat| $valPat:icasesPat)
  evalTactic (← `(tactic| iintro $valIntro))
  let g₂ ← getMainGoal
  let ty₂ ← g₂.withContext do instantiateMVars (← g₂.getType)
  let rhs :=
    if ty₂.isAppOfArity ``Iris.ProofMode.Entails' 4 then ty₂.appArg! else ty₂
  let comps :=
    if rhs.consumeMData.isAppOfArity ``Iris.BI.BIBase.wand 4 then
      Read.sepComponents rhs.consumeMData.appFn!.appArg!
    else #[]
  if comps.isEmpty then return
  let mut pats' : Array (TSyntax `icasesPat) := #[]
  let mut pureNames : Array Ident := #[]
  let mut nextUser := 1
  let mut nextConsumed := 0
  for comp in comps do
    if Read.isPure comp then
      let id := mkIdent (Name.mkSimple s!"iruleEq{fresh}")
      fresh := fresh + 1
      pureNames := pureNames.push id
      pats' := pats'.push (← mkPure id)
    else if h : nextUser < userPats.size then
      pats' := pats'.push ⟨userPats[nextUser].raw[0]⟩
      nextUser := nextUser + 1
    else if h : nextConsumed < consumed.size then
      pats' := pats'.push (← mkNamed (mkIdent consumed[nextConsumed]))
      nextConsumed := nextConsumed + 1
    else
      let id := mkFresh fresh
      fresh := fresh + 1
      pats' := pats'.push (← mkNamed id)
  if h : pats'.size = 1 then
    let onlyPat ← `(introPat| $(pats'[0]):icasesPat)
    evalTactic (← `(tactic| iintro $onlyPat))
  else
    let alts ← pats'.mapM fun q => do
      let ips : Array (TSyntax `icasesPat) := #[q]
      `(Iris.ProofMode.icasesPatAlts| $ips|*)
    evalTactic (← `(tactic| iintro ⟨$alts,*⟩))
  for id in pureNames do
    evalTactic (← `(tactic| (first | (simp only [$id:ident]; clear $id) | skip)))
  evalTactic (← `(tactic| (first | imodintro | skip)))

/-! ## Unfolding inside the proof mode -/

/-- Cast lemma for `iunfold … at`: from `ty = ty'`, the persistent replacement -/
theorem iunfoldCast {PROP : Type _} [Iris.BI PROP] {e ty ty' : PROP} (h : ty = ty') :
    e ⊢ iprop(<pers> (ty -∗ ty')) := by
  subst h
  exact Iris.BI.persistently_emp_intro.trans
    (Iris.BI.persistently_mono (Iris.BI.wand_intro Iris.BI.emp_sep.1))

open Lean Elab Tactic Meta Qq Iris.ProofMode in
/-- `iunfold f` δ-unfolds `f` in the conclusion, leaving the context — and its -/
elab "iunfold " f:ident : tactic => do
  let declName ← realizeGlobalConstNoOverloadWithInfo f
  let g ← getMainGoal
  let ty ← g.withContext do instantiateMVars (← g.getType)
  unless ty.isAppOfArity ``Iris.ProofMode.Entails' 4
      || ty.isAppOfArity ``Iris.BI.BIBase.Entails 4 do
    throwError "iunfold: goal is not an entailment{indentExpr ty}"
  let concl := ty.appArg!
  let r ← g.withContext do Meta.unfold concl declName
  let ty' := ty.appFn!.app r.expr
  let g' ← g.withContext do
    match r.proof? with
    | some h =>
        g.replaceTargetEq ty' (← mkCongrArg ty.appFn! h)
    | none => g.replaceTargetDefEq ty'
  replaceMainGoal [g']

open Lean Elab Tactic Meta Qq Iris.ProofMode in
/-- `iunfold f at H` δ-unfolds `f` inside the proof-mode hypothesis `H`. -/
elab "iunfold " f:ident " at " h:ident : tactic => do
  let declName ← realizeGlobalConstNoOverloadWithInfo f
  ProofModeM.runTactic fun mvar g => do
    let { prop, e, hyps, goal, .. } := g
    let ivar ← hyps.findWithInfo h
    let some ⟨_, hyps', pf⟩ ← hyps.replace ivar (fun _ _ ty => do
        let r ← Meta.unfold ty declName
        let some ty' ← checkTypeQ r.expr prop
          | throwError "iunfold: unfolded hypothesis is ill-typed"
        let heqE ← match r.proof? with
          | some p => pure p
          | none   => mkEqRefl ty
        let some heq ← checkTypeQ heqE q(($ty : $prop) = $ty')
          | throwError "iunfold: could not build the unfolding equality"
        let pf0 : Q($e ⊢ iprop(<pers> ($ty -∗ $ty'))) := q(AeneasIris.iunfoldCast $heq)
        return ⟨ty', pf0⟩)
      | throwError "iunfold: cannot find hypothesis {h}"
    let pf' ← addBIGoal hyps' goal
    mvar.assign q(Iris.BI.BIBase.Entails.trans $pf $pf')

end AeneasIris
