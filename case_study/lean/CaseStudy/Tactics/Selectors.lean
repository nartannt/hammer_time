import Lean.LibrarySuggestions
import CaseStudy.Tactics.MyMePo

section selectors

/-!
Tactic for running premise selectors.

Usage: `select_premises "<selector>" [n]`, where `<selector>` is one of
`"mepo"`, `"mepo_rare"`, `"sqn"`, `"combined"` and `n` is the number
of premises to request (default: 20).


Note :
- The tactic `suggestions` already exists.

-/

open Lean Meta Elab Tactic
open Lean.LibrarySuggestions

/-- Combine two selectors by concatenation (no dedup/sort). -/
def combinedSelector (s1 s2 : Selector) : Selector := fun goal config => do
  let res1 ← s1 goal config
  let res2 ← s2 goal config
  return res1 ++ res2

/-- Look up a `Selector` by string name. -/
def selectorByName : String → Option Selector
  | "mepo"        => some (mepoSelector (useRarity := false))
  | "mepo_rare"   => some (mepoSelector (useRarity := true) (p := 0.6) (c := 2.4))
  | "mymepo"      => some (HammerCases.MyMePo.myMepoSelector (useRarity := false))
  | "mymepo_rare" => some (HammerCases.MyMePo.myMepoSelector (useRarity := true))
  | "sqn"         => some sineQuaNonSelector
  | "random"      => some random
  | "currentFile" => some currentFile
  | "combined"    => some (combinedSelector
                            (mepoSelector (useRarity := false))
                            sineQuaNonSelector)
  | _             => none

/-- The reusable execution engine. -/
def runSelectorCore (selector : Selector) (n : Nat) : TacticM Unit := do
  let config : LibrarySuggestions.Config := {
    maxSuggestions := n,
    caller := some "suggest",
    filter := fun _ => pure true,
    hint := none
  }
  let goal ← getMainGoal
  let suggestions ← selector goal config
  if suggestions.isEmpty then
    logInfo "Selector found no suggestions."
  else
    let header := m!"Selector found {suggestions.size} suggestions:"
    let lines := suggestions.toList.map fun sugg =>
      m!"• {sugg.name} (score: {sugg.score})"
    logInfo <| MessageData.joinSep (header :: lines) "\n"

/--
Run a premise selector at the current goal.

Usage: `select_premises "<selector>" [n]`, where `<selector>` is one of
`"mepo"`, `"mepo_rare"`, `"sqn"`, `"combined"` and `n` is the number
of premises to request (default: 20).
-/
elab "select_premises " name:str n:(num)? : tactic => do
  let nameStr := name.getString
  let nNat := n.map (·.getNat) |>.getD 20
  match selectorByName nameStr with
  | none => throwError
      "unknown selector {nameStr}; expected one of:
        \"mepo\", \"mepo_rare\", \"sqn\", \"currentFile\""
  | some s => runSelectorCore s nNat

end selectors
