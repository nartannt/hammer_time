/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Lean.LibrarySuggestions.Basic
import Lean.LibrarySuggestions.SymbolFrequency
import Lean.Meta.Basic
import Mathlib.Tactic.Linarith
import Lean

/-!
# MePo premise selection

This is a naive implement of the MePo premise selection algorithm, from
"Lightweight relevance filtering for machine-generated resolution problems" by Meng and Paulson.

It needs to be tuned and evaluated for Lean.
-/


namespace HammerCases.PolarityMePo

open Lean Meta Lean.LibrarySuggestions

builtin_initialize registerTraceClass `mepo

def weightedScore (weight : Name → Float) (relevant candidate : NameSet) : Float :=
  let S := candidate
  let R := relevant ∩ S
  let R' := (S \ R).size.toFloat
  let M := R.foldl (fun acc n => acc + weight n) 0
  M / (M + R')

-- This function is taken from the MePo paper and needs to be tuned.
def weightFunction (n : Nat) := 1.0 + 2.0 / (n.log2.toFloat + 1.0)

def frequencyScore (frequency : Name → Nat) (relevant candidate : NameSet) : Float :=
  weightedScore (fun n => weightFunction (frequency n)) relevant candidate

def unweightedScore (relevant candidate : NameSet) : Float := 
  weightedScore (fun _ => 1) relevant candidate


-- Given an expression, we want to collect all of the constants it contains,
-- annotated by their polarity If a constant is found under an equality, its
-- polarity is set to None because the relevance of an equation to a fact is
-- orthogonal the fact's constant's polarities If a constant is found under an
-- equivalence, its polarity is also set to None, because this constant appears
-- both positively and negatively
partial def signedConstants (expr : Expr) : NameSet × NameSet :=
  let rec exprFold (expr: Expr) (polarity: Bool) : NameSet × NameSet :=
    match expr with
      -- interesting suggestion: ignore the polarity for t because it is likely
      -- to not be polarity-relevant (eg: Nat and friends)
      | Expr.forallE _ t b _ => 
        let (t_pos, t_neg) := exprFold t (!polarity)
        let (b_pos, b_neg) := exprFold b polarity
        (b_pos ++ t_neg, b_neg ++ t_pos)
      | Expr.lam _ t b _     =>
        let (t_pos, t_neg) := exprFold t polarity
        let (b_pos, b_neg) := exprFold b polarity
        (b_pos ++ t_pos, b_neg ++ t_neg)
      | Expr.letE _ t v b _  => 
        let (t_pos, t_neg) := exprFold t polarity
        let (b_pos, b_neg) := exprFold b polarity
        let (v_pos, v_neg) := exprFold v polarity
        (b_pos ++ t_pos ++ v_pos, b_neg ++ t_neg ++ v_neg)
      | Expr.proj _ _ e      =>
        let e := exprFold e polarity
        e
      | Expr.const n _       => 
        if polarity then
          (NameSet.insert NameSet.empty n, NameSet.empty)
        else
          (NameSet.empty, NameSet.insert NameSet.empty n)
      -- 3 cases:
      --    - l is Not: polarity is flipped for args
      --    - l is a Prop, then, polarity for args is not defined in general
      --    - otherwise, propagate as expected
      | Expr.app _ _         => 
       match expr.getAppFnArgs with
        -- not case
        | (``Not, #[arg]) => 
          let (arg_pos, arg_neg) := exprFold arg (!polarity)
          if polarity then
            (NameSet.insert arg_pos ``Not , arg_neg)
          else
            (arg_pos, NameSet.insert arg_neg ``Not)
        | (name, args) =>
          let (arg_pos, arg_neg) := 
            -- Prop, polarity of arguments may be undefined
            if expr.isProp then
              let all_consts := args.foldl 
                  (fun set arg ↦ (NameSet.ofArray arg.getUsedConstants) ++ set) NameSet.empty
              (all_consts, all_consts)
            else
              args.foldl (fun acc arg ↦ 
                let (arg_pos, arg_neg) := exprFold arg polarity
                let (acc_pos, acc_neg) := acc
                (arg_pos ++ acc_pos, arg_neg ++ acc_neg)) (NameSet.empty, NameSet.empty)
          -- function constant still has a defined polarity
          if polarity then
            (NameSet.insert arg_pos name , arg_neg)
          else
            (arg_pos, NameSet.insert arg_neg name)
      | _                    => (NameSet.empty, NameSet.empty)
      --termination_by sizeOf expr
  exprFold expr true

--def getSignedConstants (candidate: Name) (ci: ConstantInfo) : (Name × NameSet) :=

def polariseScore (score : NameSet → NameSet → Float) : 
    (NameSet × NameSet) → (NameSet × NameSet) → Float :=
  fun ( relevant candidate : (NameSet × NameSet)) ↦
    let (relevant_pos, relevant_neg)   := relevant
    let (candidate_pos, candidate_neg) := candidate
    let pos_score := score relevant_pos candidate_pos
    let neg_score := score relevant_neg candidate_neg
    (pos_score + neg_score) / 2

open Lean Meta MVarId in
def getSignedConstants (g : MVarId) : MetaM (NameSet × NameSet) := withContext g do
  let goalConsts := (← g.getType).getUsedConstantsAsSet
  let mut hypConsts := NameSet.empty
  for t in (← getLocalHyps) do
    hypConsts := hypConsts ∪ (← inferType t).getUsedConstantsAsSet
  return (goalConsts, hypConsts)

def mepo (initialRelevant : NameSet × NameSet) (score : NameSet → NameSet → Float) 
    (accept : ConstantInfo → CoreM Bool) (maxSuggestions : Nat) (p : Float) (c : Float)
    (polarise: Bool)
    : CoreM (Array Suggestion) := do
  let env ← getEnv
  let mut p := p
  let mut candidates := #[]
  let mut (relevantPos, relevantNeg) := initialRelevant
  let mut accepted : Array Suggestion := {}
  for (n, ci) in env.constants do
    if ← accept ci then
      candidates := candidates.push (n, signedConstants ci.type)
  if !polarise then
    relevantPos := relevantPos ++ relevantNeg
    relevantNeg := NameSet.empty
    candidates := candidates.map 
      (fun (n, (candPos, candNeg)) => (n, (candPos ++ candNeg, NameSet.empty)))
  while candidates.size > 0 && accepted.size < maxSuggestions do
    trace[mepo] m!"Considering candidates with threshold {p}."
    trace[mepo] m!"Current pos relevant set: {relevantPos.toList}."
    trace[mepo] m!"Current neg relevant set: {relevantNeg.toList}."
    let (newAccepted, candidates') := candidates.map
      (fun (n, c) => (n, c, (polariseScore score) (relevantPos, relevantNeg) c))
      |>.partition fun (_, _, s) => p ≤ s
    if newAccepted.isEmpty then return accepted
    trace[mepo] m!"Accepted {newAccepted.map fun (n, _, s) => (n, s)}."
    accepted := newAccepted.foldl (fun acc (n, _, s) => acc.push { name := n, score := s }) accepted
    candidates := candidates'.map fun (n, c, _) => (n, c)
    (relevantPos, relevantNeg) := newAccepted.foldl (
        fun (accPos, accNeg) (_, (nsPos, nsNeg), _) => 
            (accPos ++ nsPos, accNeg ++ nsNeg)) (relevantPos, relevantNeg)
    p := p + (1 - p) / c
  return accepted.qsort (fun a b => a.score > b.score)


open Lean Meta MVarId in
def getRelevantSignedConstants (g : MVarId) : MetaM (NameSet × NameSet) := withContext g do
  let goalConsts ← (← g.getType).relevantConstantsAsSet
  let mut hypConsts := NameSet.empty
  for t in (← getLocalHyps) do
    hypConsts := hypConsts ∪ (← (← inferType t).relevantConstantsAsSet)
  return (goalConsts, hypConsts)

-- The values of p := 0.6 and c := 2.4 are taken from the MePo paper, and need to be tuned.
public def mepoSelector (useRarity : Bool) (p : Float := 0.6) (c : Float := 2.4)
  (polarise : Bool := false) : Selector := 
  fun g config => do
      -- TODO
      let constants ← getRelevantSignedConstants g
      let env ← getEnv
      let score ← if useRarity then do
        let frequency ← symbolFrequencyMap
        pure <| frequencyScore (fun n => frequency.getD n 0)
      else
        pure <| unweightedScore
      let accept := fun ci => return !isDeniedPremise env ci.name
      let suggestions ← mepo constants score accept config.maxSuggestions p c polarise
      let suggestions := suggestions
        |>.reverse  -- we favor constants that appear at the end of `env.constants`
      return suggestions.take config.maxSuggestions

end HammerCases.PolarityMePo
