import Definitions.Com
import Hammer

example (s: State) : (("x" ::= (AExp.num 5));; ("y" ::= (AExp.var "x")), s) ==> s["x" ↦ 5]["y" ↦ 5] := by
  try hammer [BigStep.seq, BigStep.assign]
  apply BigStep.seq <;> apply BigStep.assign

example (s: State) (t: State) (b: BExp) : (((IF b THEN Com.skip ELSE Com.skip), s) ==> t) -> t = s := by
  hammer
  sorry

theorem ite_skip_2 (s: State) (t: State) (b: BExp) : (((IF b THEN Com.skip ELSE Com.skip), s) ==> t) -> t = s := by
  intro h
  cases h with
  | if_true _ _ _ _ _ hcond hbody => 
    cases hbody
    hammer
  | if_false _ _ _ _ _ hcond hbody =>
    cases hbody
    hammer

example (x: String) (a: AExp) (s: State) (s': State) :  (((x ::= a), s) ==> s' ) <-> (s' = s[x ↦ (aeval a s)]) := by
  hammer
  sorry

theorem assign_sim (x: String) (a: AExp) (s: State) (s': State) :  (((x ::= a), s) ==> s' ) <-> (s' = s[x ↦ (aeval a s)]) := by
  constructor
  {
    intro h
    cases h
    hammer
  }
  {
    hammer
  }

theorem seq_assoc : (((c1;; c2);; c3, s) ==> s') <-> ((c1;; (c2;; c3), s) ==> s') := by
  constructor
  {
    intro h
    hammer
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
        cases hb; apply BigStep.while_true <;> assumption
    | if_false _ _ _ _ _ _ hb =>
        have heq : (s = t) := by hammer; sorry
        hammer [BigStep.while_false]
  }

theorem unfold_while (c: Com) (b: BExp) : ((WHILE b DO c) ~ (IF b THEN c;; WHILE b DO c ELSE Com.skip)) := by
  hammer [BigStep.while_false, BigStep.if_true, BigStep.skip, BigStep.if_false, BigStep.seq, BigStep.while_true]
  repeat sorry

theorem triv_if (c: Com) (b: BExp): ((IF b THEN c ELSE c) ~ c) := by
  hammer [BigStep.if_true, BigStep.if_false]
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
    | skip => cases rn; hammer; sorry
    | assign => cases rn; hammer; sorry
    | seq _ _ _ t' _ _ _ ih ih' => 
      cases rn
      --hammer -- cannot run tactic because it returns an error and the file doesn't compile
      sorry
    | if_true _ _ _ _ _ _ _ ih =>
      cases rn
      hammer
      sorry
    | if_false cond ci ce s' t' hcond hobdy ih =>
      cases rn
      hammer
      sorry
    | while_true _ _ _ t' _ _ _ _ ih ih' => 
      cases rn
      -- hammer
      sorry
    | while_false =>
      cases rn; hammer; sorry

