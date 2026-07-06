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

-- the Q and P recursors / constructors are irrelevant to the goal
set_library_suggestions (selectorByName "mepo_polarised").get!
example : Q := by
  have h : P := by sorry
  have h': Q → P := by sorry
  -- polarised mepo selects none of them
  hammer []

set_library_suggestions (selectorByName "mepo").get!
example : Q := by
  have h : P := by sorry
  have h': Q → P := by sorry
  -- baseline mepo selects irrelevant premises
  hammer []



-- the Q and P recursors / constructors are necessary to prove the goal
set_library_suggestions (selectorByName "mepo_polarised").get!
example : Q := by
  have h : P := by sorry
  have h': P → Q := by sorry
  -- when they are useful, polarised mepo selects the same premises as mepo
  hammer []

set_library_suggestions (selectorByName "mepo").get!
example : Q := by
  have h : P := by sorry
  have h': P → Q := by sorry
  hammer []
