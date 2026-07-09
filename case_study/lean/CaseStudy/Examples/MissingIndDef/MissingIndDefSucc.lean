import MyHammer

namespace HammerCases.MissingIndDef.Succ

set_option trace.auto.tptp.printQuery true
set_option trace.auto.tptp.result true
set_option myhammer.preprocessingDefault "no_preprocessing"
set_option myhammer.disableAesopDefault true
set_option myhammer.autoPremisesDefault 16
set_option trace.myhammer.premises true
set_option trace.debug true
set_option pp.rawOnError true
-- set_option trace.mepo true

open Lean LibrarySuggestions
set_library_suggestions mepoSelector (useRarity := false)

inductive A : Type

inductive B : A -> Prop where
  | b x : B x

example : forall x: A, B x := by
  myhammer [] {autoPremises:= 16, disableAesop := true}

namespace HammerCases.MissingIndDef.Succ
