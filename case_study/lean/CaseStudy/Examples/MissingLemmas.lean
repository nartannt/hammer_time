import Hammer
import Mathlib.Tactic.MkIffOfInductiveProp
import Lean.Expr
import CaseStudy.Tactics.MyMePo
import CaseStudy.Tactics.Selectors

set_option trace.auto.tptp.printQuery true
set_option trace.auto.tptp.result true
set_option hammer.preprocessingDefault "no_preprocessing"
set_option hammer.disableAesopDefault true
set_option hammer.autoPremisesDefault 16
set_option trace.hammer.premises true
set_option trace.debug true
set_option pp.rawOnError true

inductive A : Type

--@[mk_iff]
inductive B : A -> Prop where
  | b x : B x

#check B.b

--def test := do
--  let lctx ← Lean.MonadLCtx.getLCtx
--  lctx.forM fun elem: Lean.LocalDecl => do
--    let elemExpr := elem.toExpr
--    dbg_trace f!"local declaration: {elemExpr}"

elab "list_local_decls" : tactic => do
    let ctx ← Lean.MonadLCtx.getLCtx -- get the local context.
    ctx.forM fun decl: Lean.LocalDecl => do
      let declExpr := decl.toExpr -- Find the expression of the declaration.
      let declName := decl.userName -- Find the name of the declaration.
      dbg_trace f!"+ local decl: name: {declName} | expr: {declExpr}"

elab "list_constants" : tactic => do
    let env ← Lean.MonadEnv.getEnv
    let constants := env.constants
    for cnst in constants do
      let (cnstName, _cnstInfo) := cnst
      if cnstName.toString.contains "__" then
        dbg_trace "name: {cnstName}"

open Mathlib.Tactic.MkIff Lean Meta Elab
elab "list_iff_ind" : tactic => do
  let env ← Lean.MonadEnv.getEnv -- get the local environment
  let constants := env.constants -- get the local constants.
  for cnst in constants do
    let (cnstName, cnstInfo) := cnst
    match cnstInfo with
      | .inductInfo inductVal =>
        let indValTerm : Term ← PrettyPrinter.delab inductVal.type
        let indValSyntax : Syntax := indValTerm.raw
        try MetaM.run' do mkIffOfInductivePropImpl cnstName (cnstName.decapitalize.toString ++ "____iff").toName indValSyntax
        catch _ => pure ()
      | _ => pure ()

example : forall x: A, B x := by
  list_iff_ind

  select_premises "mymepo"
  select_premises "mepo"
  hammer [] {}
