import Definitions.Com
import Hammer

example (s: State) : (("x" ::= (AExp.num 5));; ("y" ::= (AExp.var "x")), s) ==> s["x" ↦ 5]["y" ↦ 5] := by
  try hammer [BigStep.seq, BigStep.assign]
  apply BigStep.seq <;> apply BigStep.assign

theorem ite_skip (s: State) (t: State) (b: BExp) : (((IF b THEN Com.skip ELSE Com.skip), s) ==> t) -> t = s := by
  intro bs
  cases bs with
    | if_true  _ _ _ _ _ _ hb => cases hb; rfl
    | if_false _ _ _ _ _ _ hb => cases hb; rfl


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
  constructor <;> 
  intro h <;>
  cases h with 
  | seq _ _ _ _ _ h1 h2
  {
    cases h1 
    hammer [BigStep.seq]
  }
  {
    cases h2 
    repeat apply BigStep.seq <;> try assumption
  }

theorem unfold_while (c: Com) (b: BExp) : ((WHILE b DO c) ~ (IF b THEN c;; WHILE b DO c ELSE Com.skip)) := by
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
        cases hb; apply BigStep.while_false; assumption
  }


theorem triv_if (c: Com) (b: BExp): ((IF b THEN c ELSE c) ~ c) := by
  intros s t
  constructor
  intro h; cases h <;> assumption 
  intro h
  cases hc: (beval b s)
  hammer [BigStep.if_true, BigStep.if_false]
  hammer [BigStep.if_true, BigStep.if_false]

syntax "ass_trivial" : tactic
macro_rules | `(tactic | ass_trivial) => `(tactic | (assumption; try trivial))

syntax "if_true_false" : tactic
macro_rules | `(tactic | if_true_false) => `(tactic |  (first | apply BigStep.if_true; ass_trivial | apply BigStep.if_false; ass_trivial))

syntax "ite_both" : tactic
macro_rules 
  | `(tactic| ite_both )  => `(tactic | 
        first | (apply BigStep.if_true; ass_trivial); if_true_false | (apply BigStep.if_false; ass_trivial); (try if_true_false))

theorem commute_if: (IF b1 THEN (IF b2 THEN c11 ELSE c12) ELSE c2) 
   ~ 
   (IF b2 THEN (IF b1 THEN c11 ELSE c2) ELSE (IF b1 THEN c12 ELSE c2)) := by
  intros s t
  constructor
  intro h
  cases h with
    | if_true  _ _ _ _ _ _ hb => {
      cases hb <;> ite_both
    }
    | if_false => {
      by_cases (beval b2 s = true) <;> ite_both
    }

  intro h
  cases h with
    | if_true  _ _ _ _ _ _ hb => {
      cases hb <;> ite_both
    }
    | if_false _ _ _ _ _ _ hb => {
      cases hb <;> ite_both
    }


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
        try hammer
        hammer [BigStep.while_false]
      }
      | while_true cond d s' t' u hcond hb hr ih_c ih_r=> {
        cases rn
        try hammer
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
    | skip => cases rn; cases h_1; rfl
    | assign => cases rn; cases h_1; rfl
    | seq _ _ _ t' _ _ _ ih ih' => 
      cases rn
      cases h_1 with | seq _ _ _ v _ _ ht'
      have h_mid : (v = t') := by
        apply ih; assumption; rfl
      hammer
    | if_true _ _ _ _ _ _ _ ih =>
      cases rn
      cases h_1 with
        | if_true => hammer
        | if_false => trivial
    | if_false cond ci ce s' t' hcond hobdy ih =>
      cases rn
      cases h_1 with
        | if_true => trivial
        | if_false => hammer
    | while_true _ _ _ t' _ _ _ _ ih ih' => 
      cases rn
      cases h_1 with
        | while_true _ _ _ v _ _ hbody _ => hammer
        | while_false => trivial
    | while_false =>
      cases rn; cases h_1 <;> trivial
