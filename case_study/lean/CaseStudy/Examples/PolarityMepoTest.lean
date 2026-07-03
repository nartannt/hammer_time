import Hammer
import CaseStudy.Tactics.Selectors

open Lean LibrarySuggestions


set_option trace.auto.tptp.printQuery true
set_option trace.auto.tptp.result true
set_option hammer.preprocessingDefault "no_preprocessing"
set_option hammer.disableAesopDefault true
set_option hammer.disableGrindDefault true
set_option hammer.autoPremisesDefault 16
set_option trace.hammer.premises true
set_option trace.debug true
set_option pp.rawOnError true
set_option trace.mepo true


inductive P : Prop
inductive Q : Prop
--public theorem p : P := by sorry
--public theorem p_imp_q : P → Q := by sorry

-- the premises h and h' are irrelevant to the goal
set_library_suggestions (selectorByName "mepo_polarised").get!
example : Q := by
  have h : P := by sorry
  have h': Q → P := by sorry
  hammer []

set_library_suggestions mepoSelector (useRarity := false)
example : Q := by
  have h : P := by sorry
  have h': Q → P := by sorry
  hammer []



-- the premises h and h' are necessary to prove the goal
set_library_suggestions (selectorByName "mepo_polarised").get!
example : Q := by
  have h : P := by sorry
  have h': P → Q := by sorry
  hammer []

set_library_suggestions (selectorByName "mepo").get!
example : Q := by
  have h : P := by sorry
  have h': P → Q := by sorry
  hammer []
