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

set_option profiler true

inductive A : Type

inductive B : A -> Prop where
  | b x : B x

elab "list_constants" : tactic => do
    let env ← Lean.MonadEnv.getEnv
    let constants := env.constants
    for cnst in constants do
      let (cnstName, _cnstInfo) := cnst
      if cnstName.toString.contains "__" then
        dbg_trace "name: {cnstName}"

-- TODO we want to apply this tactic after the premise selection to avoid generating useless lemmas
-- but we also want to do it before so that the premise selector can chose them
-- given how long the tactic takes to execute we may want to only apply it to selected definitions
open Mathlib.Tactic.MkIff Lean Meta Elab
elab "list_iff_ind" : tactic => do
  let env ← Lean.MonadEnv.getEnv -- get the local environment
  let constants := env.constants -- get the local constants.
  for cnst in constants do
    let (cnstName, cnstInfo) := cnst
      match cnstInfo with
        | .inductInfo inductVal =>
          if !cnstName.toString.contains "Lean." &&
             !cnstName.toString.contains "Std." then
            --dbg_trace "{cnstName}"
            let indValTerm : Term ← PrettyPrinter.delab inductVal.type
            let indValSyntax : Syntax := indValTerm.raw
            try MetaM.run' do 
              mkIffOfInductivePropImpl cnstName (cnstName.decapitalize.toString ++ "____iff").toName indValSyntax
            catch _ => pure ()
          else pure ()
        | _ => pure ()

example : forall x: A, B x := by
  list_iff_ind
  hammer [] {}
