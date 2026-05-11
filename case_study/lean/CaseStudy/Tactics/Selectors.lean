import Lean.LibrarySuggestions

/-
TODO:
Unify tactics to have the following pattern
`suggest "selector" "number of premises"`.

-/

section selectors

open Lean Meta Elab Tactic
open Lean.LibrarySuggestions

/-- The reusable execution engine. -/
def runSelectorCore (selector : Selector) : TacticM Unit := do
  let goal ← getMainGoal
  let config : LibrarySuggestions.Config := {
    maxSuggestions := 10,
    caller := some "run_selector",
    filter := fun _ => pure true,
    hint := none
  }

  let suggestions ← selector goal config

  if suggestions.isEmpty then
  logInfo "Selector found no suggestions."
  else
    let header := m!"Selector found {suggestions.size} suggestions:"
    -- Create a list of MessageData for each suggestion
    let lines := suggestions.toList.map fun sugg =>
      m!"• {sugg.name} (score: {sugg.score})"
    -- Join the header and the lines with newlines
    logInfo <| MessageData.joinSep (header :: lines) "\n"


---------------------------------------------------------
-- Tactic Wrappers
---------------------------------------------------------

-- 1. Standard MePo
elab "run_mepo" : tactic =>
  runSelectorCore (mepoSelector (useRarity := false))

-- 2. Rare-weighted MePo
elab "run_mepo_rare" : tactic =>
  runSelectorCore (mepoSelector (useRarity := true) (p := 0.6) (c := 2.4))

-- 3. Sine Qua Non Selector (from the file in your image!)
elab "run_sqn" : tactic =>
  runSelectorCore sineQuaNonSelector

-- 4. Custom Combiner (Fixing the previous error)
def combinedSelector (s1 s2 : Selector) : Selector := fun goal config => do
  let res1 ← s1 goal config
  let res2 ← s2 goal config
  -- Append the arrays together (in a real scenario, you would dedup/sort here)
  return res1 ++ res2

elab "run_combined" : tactic => do
  let s1 := mepoSelector (useRarity := false)
  let s2 := sineQuaNonSelector
  runSelectorCore (combinedSelector s1 s2)

end selectors
