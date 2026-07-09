import Hammer

namespace HammerCases.MissingIndDef.Fail

--set_option trace.auto.tptp.printQuery true
--set_option trace.auto.tptp.result true
set_option hammer.preprocessingDefault "no_preprocessing"
set_option hammer.disableAesopDefault true
set_option hammer.disableGrindDefault true
set_option hammer.autoPremisesDefault 16

set_option trace.hammer.premises true
set_option trace.debug true
set_option pp.rawOnError true
set_option trace.mepo true

inductive A : Type

inductive B : A -> Prop where
  | b x : B x

open Lean LibrarySuggestions
set_library_suggestions mepoSelector (useRarity := false)

example : forall x: A, B x := by
  hammer [] {autoPremises:= 16, disableAesop := true}

namespace HammerCases.MissingIndDef.Fail
