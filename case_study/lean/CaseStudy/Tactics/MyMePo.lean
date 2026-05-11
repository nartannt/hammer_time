import Lean.LibrarySuggestions

/-!
# MyMePo

A custom reimplementation of MePo (Meng-Paulson) premise selection.

Differences from `Lean.LibrarySuggestions.mepoSelector`:

* **Iteration tracking.** Each accepted constant is tagged with the iteration
  in which it crossed the threshold. Iter 1 = constants whose types overlap
  the *original* goal symbols; iter k = constants reachable after k-1 rounds
  of relevant-set expansion.

* **Symmetric symbol extraction.** The goal's seed set is computed with
  `relevantConstantsAsSet` (which skips proof terms and instance-implicit
  arguments). For candidates we use the cheap syntactic `getUsedConstantsAsSet`
  and then strip instance constants (`Lean.Meta.isInstanceCore env nm`). This
  avoids the per-candidate `MetaM`/WHNF cost of `relevantConstantsAsSet` while
  preserving the symmetric "instance args don't count" semantics that the
  stdlib version breaks.

* **No internal score sort.** Results are returned in
  (iter asc, score desc, envIdx desc) order so the most goal-proximate batch
  comes first, with later-defined constants preferred within a tie. Since
  `env.constants` iterates imports before locals, this surfaces project-local
  lemmas above deeply-imported library ones that score identically.

## Performance TODO

Baseline before any work: ~8 s/call. Phase costs measured on the `add2`
goal: env iter ~0.5 s, deny filter ~1.8 s, `relevantConstantsAsSet` walk
~5.5 s, iter loop ~0.2 s.

Tier 1 — big wins

1. **[DONE]** Swap `relevantConstantsAsSet` (MetaM, WHNF) for
   `getUsedConstantsAsSet` + post-filter via `Lean.Meta.isInstanceCore`
   on the candidate side. Saves ~5.5 s. Result: 8 s → 2.7 s/call.

2. **[DONE]** Cache the candidate pool in a process-wide `IO.Ref`,
   keyed by `(mainModule, |imports|, |locals|)`. Skips the deny+symbol
   pass on warm calls. Saves ~2.5 s. Result on warm calls: 2.7 s → 0.11 s.

3. **[TODO]** Iterate the local map (`env.constants.map₂`) first; only
   fall through to imports if the cap is not yet filled. For small caps
   on locally-rooted goals (the common case), should let warm calls
   reach near-zero overhead.

Tier 2 — moderate wins

4. **[TODO]** Parallelise the cold pool build via `Task`/IO chunks
   across `env.constants`. Pure data, safe to do off the main thread.
   Expected ~3× cold-call speedup on multi-core.

5. **[TODO]** Pre-filter candidates by `ConstantInfo` kind
   (`isTheorem || isDefn`). Drops axioms, type formers, ctors from the
   pool. Cuts ~30 % of the symbol walk and shrinks iter-loop work.

Tier 3 — small wins

6. **[TODO]** Swap `NameSet` (RBTree) for `NameHashSet` in the hot
   intersection/difference paths. Marginal for small relevant sets;
   may matter once `relevant` grows in later iters.

7. **[TODO]** Fuse `candidates.map` + `partition` into a single pass
   to avoid one intermediate array allocation per iter.

8. **[TODO]** Early-reject in scoring: if `|candidate| - |R|` is large
   enough that even M = |candidate| can't clear the threshold, skip
   the divide.

Verified non-options (don't pursue):

* Inlining `isDeniedPremise` with hoisted extension states. Measured
  3× slower than the stdlib direct call — closure indirection beats
  the savings from hoisting `.getState env`.
* `relevantConstantsAsSet` on candidates. Already settled in #1.
-/

namespace HammerCases.MyMePo

open Lean Meta Lean.LibrarySuggestions

/-- An accepted candidate, tagged with the iteration in which it was admitted
    and its position in `env.constants`. Higher `envIdx` = later-defined. -/
structure IterSuggestion where
  name   : Name
  score  : Float
  iter   : Nat
  envIdx : Nat
  deriving Inhabited

def IterSuggestion.toSuggestion (s : IterSuggestion) : Suggestion :=
  { name := s.name, score := s.score }

/-- `M / (M + R')`, where `M = Σ weight n  for n ∈ relevant ∩ candidate`
    and `R' = |candidate \ relevant|`. -/
def weightedScore (weight : Name → Float) (relevant candidate : NameSet) : Float :=
  let R := relevant ∩ candidate
  let R' := (candidate \ R).size.toFloat
  let M := R.foldl (fun acc n => acc + weight n) 0
  if M + R' == 0 then 0 else M / (M + R')

def unweightedScore : NameSet → NameSet → Float :=
  weightedScore (fun _ => 1)

/-! ## Candidate-pool cache

The pool (deny-filtered, symbol-extracted, env-indexed) is a pure function
of the environment. Cache it in a process-wide `IO.Ref` keyed by a cheap
fingerprint: `(mainModule, |imports|, |locals|)`. The fingerprint changes
whenever a new local declaration is added (so the cache invalidates within
the same file as it grows), or whenever we switch to a different file. -/

abbrev EnvFingerprint := Name × Nat × Nat

/-- Count of locally-defined constants. `map₂` is a `PersistentHashMap`
without an O(1) size, but locals are tiny (~10s of entries), so folding is
cheap. -/
private def localCount (env : Environment) : Nat :=
  env.constants.map₂.foldl (fun acc _ _ => acc + 1) 0

def envFingerprint (env : Environment) : EnvFingerprint :=
  (env.mainModule, env.imports.size, localCount env)

/-- The cached pool. `none` means uninitialised. -/
initialize candidatePoolCache :
    IO.Ref (Option (EnvFingerprint × Array (Name × NameSet × Nat))) ←
  IO.mkRef none

/-- Walk `env.constants`, deny-filter, extract the symbol set for each
accepted candidate. Pure function of the environment. -/
def buildCandidatePool (env : Environment) : Array (Name × NameSet × Nat) := Id.run do
  let mut candidates : Array (Name × NameSet × Nat) := #[]
  let mut envIdx : Nat := 0
  for (n, ci) in env.constants do
    if !isDeniedPremise env n then
      let raw := ci.type.getUsedConstantsAsSet
      let syms : NameSet := raw.foldl (init := {}) fun acc nm =>
        if Lean.Meta.isInstanceCore env nm then acc else acc.insert nm
      candidates := candidates.push (n, syms, envIdx)
    envIdx := envIdx + 1
  return candidates

/-- Get the candidate pool for `env`, building it on first use or whenever
the env fingerprint has changed. -/
def getOrBuildCandidatePool (env : Environment) :
    IO (Array (Name × NameSet × Nat)) := do
  let fp := envFingerprint env
  match (← candidatePoolCache.get) with
  | some (fp', pool) =>
    if fp == fp' then return pool
  | none => pure ()
  let pool := buildCandidatePool env
  candidatePoolCache.set (some (fp, pool))
  return pool

/-- Core iteration. Returns accepted constants in iteration order, tagged with
    the iter index they were accepted at. -/
def runIterations
    (initialRelevant : NameSet)
    (score           : NameSet → NameSet → Float)
    (maxSuggestions  : Nat)
    (p0              : Float := 0.6)
    (c               : Float := 2.4) :
    MetaM (Array IterSuggestion) := do
  let env ← getEnv
  let mut candidates ← getOrBuildCandidatePool env
  let mut relevant : NameSet := initialRelevant
  let mut p        : Float := p0
  let mut iter     : Nat := 1
  let mut accepted : Array IterSuggestion := #[]
  while candidates.size > 0 && accepted.size < maxSuggestions do
    let scored := candidates.map fun (n, c, idx) => (n, c, idx, score relevant c)
    let (newAccepted, remaining) := scored.partition fun (_, _, _, s) => p ≤ s
    if newAccepted.isEmpty then break
    accepted := newAccepted.foldl
      (fun acc (n, _, idx, s) =>
        acc.push { name := n, score := s, iter, envIdx := idx }) accepted
    candidates := remaining.map fun (n, c, idx, _) => (n, c, idx)
    relevant := newAccepted.foldl (fun acc (_, ns, _, _) => acc ++ ns) relevant
    p    := p + (1 - p) / c
    iter := iter + 1
  return accepted

/-- Selector: run MyMePo on the current goal and return up to `cfg.maxSuggestions`
    entries, ordered (iter asc, score desc). -/
def myMepoSelector
    (useRarity : Bool := false)
    (p         : Float := 0.6)
    (c         : Float := 2.4) : Selector := fun g cfg => do
  -- Wrap the goal so motive-mvars from `induction`/`cases` are instantiated
  -- before symbol extraction.
  g.withContext do
    let newType ← instantiateMVars (← g.getType)
    let g' ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar newType
    let gid := g'.mvarId!
    let initialRelevant ← gid.getRelevantConstants
    let score : NameSet → NameSet → Float ←
      if useRarity then do
        let frequency ← symbolFrequencyMap
        pure <| weightedScore (fun n =>
          let f := frequency.getD n 0
          1.0 + 2.0 / (f.log2.toFloat + 1.0))
      else
        pure unweightedScore
    let entries ← runIterations initialRelevant score cfg.maxSuggestions p c
    let sorted := entries.qsort fun a b =>
      if a.iter != b.iter then a.iter < b.iter
      else if a.score != b.score then a.score > b.score
      else a.envIdx > b.envIdx
    return (sorted.map IterSuggestion.toSuggestion).extract 0 cfg.maxSuggestions

end HammerCases.MyMePo
