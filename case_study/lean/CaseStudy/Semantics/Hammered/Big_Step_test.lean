import CaseStudy.Semantics.Definitions.Com_test
import Hammer

set_option trace.auto.tptp.printQuery true
set_option trace.auto.tptp.result true

example (s: State) : (("x" ::= (AExp.num 5));; ("y" ::= (AExp.var "x")), s) ==> s["x" ↦ 5]["y" ↦ 5] := by
  -- try hammer [BigStep.seq, BigStep.assign]
  apply BigStep.seq <;> apply BigStep.assign

example (s: State) (t: State) (b: BExp) : (((IF b THEN Com.skip ELSE Com.skip), s) ==> t) -> t = s := by
  -- hammer
  sorry

theorem inversion_skip (s: State) (t: State) : ((SKIP, s) ==> t) -> t = s := by
    --try -- hammer
    intro h; cases h; rfl
theorem inversion_asign (x: String) (a: AExp) (s: State) (t: State) : ((Com.assign x a, s) ==> t) -> t = s[x ↦ (aeval a s)]
  := by
    intro h
    try -- hammer
    -- hammer
    cases h
    rfl
theorem inversion_seq (s: State) (t: State) (c1: Com) (c2: Com) :
    ((c1;;c2, s) ==> t) -> (exists s', ((c1, s)==> s') ∧ ((c2, s') ==> t)) := by sorry
theorem inversion_ite (cond: BExp) (ci: Com) (ce: Com) (s: State) (t: State) :
    ((IF cond THEN ci ELSE ce, s) ==> t) -> (( (beval cond s) ∧ ((ci, s) ==> t))
                                            ∨(¬(beval cond s) ∧ ((ce, s) ==> t)) ) := by
                      intros h
                      cases h with
                        | if_true cond _ _ _ _ hcond hbody => {
                          left
                          trivial
                        }
                        | if_false cond _ _ _ _ hcond hbody => {right; trivial}
theorem inversion_while (cond: BExp) (cl: Com) (s: State) (t: State) :
    ((WHILE cond DO cl, s) ==> t) -> (  (exists s', (beval cond s) ∧ ((cl, s) ==> s') ∧ ((WHILE cond DO cl, s') ==> t) )
                                     ∨ (¬(beval cond s) ∧ (t = s)) ) := by sorry

theorem inversion_bs (c: Com) (s: State) (t: State) : ((c, s) ==> t) ->
   (c = SKIP) ∧ (t = s)
  ∨ (exists x a, (c = (Com.assign x a)) ∧ (t = s[x ↦ (aeval a s)]))
  ∨ (exists c1 c2 s', (c = c1;;c2) ∧ ((c1, s) ==> s') ∧ ((c2, s') ==> t))
  ∨ (exists cond ci ce, (c = IF cond THEN ci ELSE ce) ∧ (beval cond s) ∧ ((ci, s) ==> t))
  ∨ (exists cond ci ce, (c = IF cond THEN ci ELSE ce) ∧ (¬ (beval cond s)) ∧ ((ce, s) ==> t))
  ∨ (exists cond cl s', (c = WHILE cond DO cl) ∧ (beval cond s) ∧ ((cl, s)==> s') ∧ ((c, s') ==> t))
  ∨ (exists cond cl, (c = WHILE cond DO cl) ∧ (¬ (beval cond s)) ∧ (t = s)) := by
    intro h
    cases h with
      | skip => { aesop }
      | assign => { aesop }
      | seq c1 c2 _ s' _ hl hr => { sorry }
      | if_true cond ci ce _ _ hcond hbody => { sorry }
      | if_false cond ci ce _ _ hcond hbody => { sorry }
      | while_true cond cl _ s' _ hcond hbody hrest => { sorry }
      | while_false cond cl _ s' => { sorry }


theorem ite_skip_2 (s: State) (t: State) (b: BExp) : (((IF b THEN Com.skip ELSE Com.skip), s) ==> t) -> t = s := by
  --hammer [inversion_skip, inversion_ite] {disableAesop := true}
  sorry

example (x: String) (a: AExp) (s: State) (s': State) :  (((x ::= a), s) ==> s' ) <-> (s' = s[x ↦ (aeval a s)]) := by
  sorry
  -- constructor
  -- { hammer [inversion_assign] {disableAesop := true} }
  -- { hammer [inversion_assign] {disableAesop := true} }

theorem assign_sim (x: String) (a: AExp) (s: State) (s': State) :  (((x ::= a), s) ==> s' ) <-> (s' = s[x ↦ (aeval a s)]) := by
  constructor
  {
    sorry
    -- hammer
    --hammer [inversion_bs] {disableAesop := true}

  }
  {
    -- try hammer [BigStep.assign] {disableAesop := true}
    intro h
    rw [h]
    apply BigStep.assign

  }
#exit
theorem seq_assoc : (((c1;; c2);; c3, s) ==> s') <-> ((c1;; (c2;; c3), s) ==> s') := by
  constructor
  {
    intro h
    -- hammer
    sorry
  }
  {
    intro h
    cases h with | seq _ _ _ s1 _ h1 ht =>
    cases ht with | seq _ _ _ s2 _ h2 h3 =>
    have hi: (((c1;;c2), s) ==> s2) := by
      apply BigStep.seq <;>
      assumption
    apply BigStep.seq <;> try assumption
  }

example (c: Com) (b: BExp) : ((WHILE b DO c) ~ (IF b THEN c;; WHILE b DO c ELSE Com.skip)) := by
  intros s t
  constructor
  {
    intro h
    cases h with
    | while_true =>
      hammer [BigStep.if_true, BigStep.seq]
    | while_false =>
      hammer [BigStep.if_false, BigStep.skip]
  }
  {
    intro h'
    cases h' with
    | if_true _ _ _ _ _ _ hb =>
        --cases hb; apply BigStep.while_true <;> assumption
        -- hammer
        hammer [BigStep.while_true]
    | if_false _ _ _ _ _ _ hb =>
        -- have heq : (s = t) := by hammer; sorry
        hammer [BigStep.while_false, inversion_skip]
  }

theorem unfold_while (c: Com) (b: BExp) : ((WHILE b DO c) ~ (IF b THEN c;; WHILE b DO c ELSE Com.skip)) := by
  hammer [inversion_ite, inversion_while, BigStep.while_false, BigStep.if_true, BigStep.skip, BigStep.if_false, BigStep.seq, BigStep.while_true]
  repeat sorry

theorem triv_if (c: Com) (b: BExp): ((IF b THEN c ELSE c) ~ c) := by
  hammer [inversion_ite, BigStep.if_true, BigStep.if_false]
  sorry

theorem commute_if: (IF b1 THEN (IF b2 THEN c11 ELSE c12) ELSE c2)
   ~
   (IF b2 THEN (IF b1 THEN c11 ELSE c2) ELSE (IF b1 THEN c12 ELSE c2)) := by
  hammer [BigStep.if_true, BigStep.if_false]
  repeat sorry


theorem sim_while_cong_aux:
  ((WHILE b DO c,s) ==> t)  -> (c ~ c') ->  ((WHILE b DO c',s) ==> t) := by
    intros h
    generalize rn : (WHILE b DO c, s) = p
    rw [rn] at h
    induction h generalizing s with
      | skip => cases rn
      | assign => cases rn
      | seq => cases rn
      | if_true => cases rn
      | if_false => cases rn
      | while_false cond d s' hcond=> {
        cases rn
        hammer [BigStep.while_false]
      }
      | while_true cond d s' t' u hcond hb hr ih_c ih_r=> {
        cases rn
        hammer [BigStep.while_true]
      }



theorem sim_while_cong: (c ~ c') -> (WHILE b DO c) ~ (WHILE b DO c') := by
  hammer

theorem sim_refl:  ( c ~ c ) := by
  hammer

theorem sim_sym:   ((c ~ c') <-> (c' ~ c)) := by
  hammer

theorem sim_trans: ( (c ~ c') -> (c' ~ c'') -> (c ~ c'') ) := by
  hammer

theorem big_step_determ: (((c,s) ==> t) ∧ ((c,s) ==> u) ) -> (u = t) := by
  intro h
  rcases h with ⟨h_0, h_1⟩
  generalize rn : (c, s) = p
  rw [rn] at h_0
  induction h_0 generalizing s u c with
    | skip => cases rn; -- hammer
    | assign => cases rn; -- hammer
    | seq _ _ _ t' _ _ _ ih ih' =>
      cases rn
      --hammer -- cannot run tactic because it returns an error and the file doesn't compile
      sorry
    | if_true _ _ _ _ _ _ _ ih =>
      cases rn
      -- hammer
      sorry
    | if_false cond ci ce s' t' hcond hobdy ih =>
      cases rn
      -- hammer
      sorry
    | while_true _ _ _ t' _ _ _ _ ih ih' =>
      cases rn
      -- -- hammer
      sorry
    | while_false =>
      cases rn; hammer
