import Hammer
import Mathlib.Tactic.MkIffOfInductiveProp
import Lean.Expr
import CaseStudy.Tactics.MyMePo
import CaseStudy.Tactics.Selectors

set_option trace.auto.tptp.printQuery true
set_option trace.auto.tptp.result true
set_option hammer.preprocessingDefault "no_preprocessing"
set_option hammer.disableAesopDefault true
set_option hammer.autoPremisesDefault 0
set_option trace.hammer.premises true
set_option trace.debug true
set_option pp.rawOnError true

set_option profiler true

inductive A : Type

inductive B : A -> Prop where
  | b x : B x


#check exists_true_left
example : forall x: A, B x := by
  hammer [ exists_true_left ] {}
