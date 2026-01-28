-- copying this here until I figure out how to do imports in lean
inductive AExp : Type where
| num : Int → AExp
| var : String → AExp
| add : AExp → AExp → AExp


inductive BExp : Type where
  | bc : Bool -> BExp
  | not : BExp -> BExp
  | and : BExp -> BExp -> BExp
  | less : AExp -> AExp -> BExp

inductive Com : Type where
| skip : Com
| assign : String → AExp → Com
| seq : Com → Com → Com
| ite : BExp → Com → Com → Com
| while : BExp → Com → Com


-- these are stolen and adapted from LoVe
def State : Type := String → Int

def aeval : AExp -> State -> Int
| AExp.num n, _ => n
| AExp.var str, s => s str
| AExp.add n m, s => (aeval n s) + (aeval m s)

def beval : BExp -> State -> Bool
  | BExp.bc b, _ => b
  | BExp.not exp, s => not (beval exp s)
  | BExp.and b_1 b_2, s => and (beval b_1 s) (beval b_2 s)
  | BExp.less n_1 n_2, s => (aeval n_1 s) < (aeval n_2 s)

def state.update (name : String) (val : Int) (s : State) : State := λname' ↦ if name' = name then val else s name'

-- some notations are stolen and adapted from LoVe lib others are stolen or inspired from https://github.com/leanprover-community/lean4-samples/blob/main/ListComprehension/README.md

--declare_syntax_cat mod_state

notation (name := eval_state) s "[" name "↦" val "]" => state.update name val s 
notation (name := seq_semicolon) s_1 ";;" s_2 => Com.seq s_1 s_2
notation (name := assign_eq) var_name "::=" expr => Com.assign var_name expr
notation (name := ite_term) "IF" cond "THEN" expr_1 "ELSE" expr_2 => Com.ite cond expr_1 expr_2
notation (name := while_term) "WHILE" cond "DO" expr => Com.while cond expr

inductive BigStep : Com × State -> State -> Prop where
  | skip (s) : BigStep (Com.skip, s) s
  | assign (x a s) :
    BigStep (Com.assign x a, s) ( s[x ↦ (aeval a s)] )
  | seq (S T s t u) (hS : BigStep (S, s) t) (hT : BigStep (T, t) u) :
    BigStep (S ;; T, s) u
  | if_true (B S T s t) (hcond : beval B s) (hbody : BigStep (S, s) t) :
    BigStep (Com.ite B S T, s) t
  | if_false (B S T s t) (hcond : ¬ (beval B s)) (hbody : BigStep (T, s) t) :
    BigStep (Com.ite B S T, s) t
  | while_true (B S s t u) (hcond : beval B s) (hbody : BigStep (S, s) t) (hrest : BigStep (Com.while B S, t) u) :
    BigStep (Com.while B S, s) u
  | while_false (B S s) (hcond : ¬ beval B s) :
    BigStep (Com.while B S, s) s

notation (name := big_step_judgement) prog_init_state_pair "==>" final_state => BigStep prog_init_state_pair final_state

set_option quotPrecheck false
notation (name := sem_equivalence) p "~" p' => forall s t, ((p, s) ==> t) <-> ((p', s) ==> t)

example (s: State) : (("x" ::= (AExp.num 5));; ("y" ::= (AExp.var "x")), s) ==> s["x" ↦ 5]["y" ↦ 5] := by
  apply BigStep.seq <;> apply BigStep.assign

theorem ite_skip (s: State) (t: State) (b: BExp) : (((IF b THEN Com.skip ELSE Com.skip), s) ==> t) -> t = s := by
  intro bs
  cases bs with
    | if_true  _ _ _ _ _ _ hb => cases hb; rfl
    | if_false _ _ _ _ _ _ hb => cases hb; rfl


theorem assign_sim (x: String) (a: AExp) (s: State) (s': State) :  (((x ::= a), s) ==> s' ) <-> (s' = s[x ↦ (aeval a s)]) := by
  constructor
  {
    intro h; cases h; rfl
  }
  {
    intro h
    rw [h]
    apply BigStep.assign
  }

theorem seq_assoc : (((c1;; c2);; c3, s) ==> s') <-> ((c1;; (c2;; c3), s) ==> s') := by
  constructor <;> 
  intro h <;>
  cases h with 
  | seq _ _ _ _ _ h1 h2
  {
    cases h1 
    repeat apply BigStep.seq <;> try assumption
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
      apply BigStep.if_true; assumption
      apply BigStep.seq <;> assumption
    | while_false =>
      apply BigStep.if_false; assumption; apply BigStep.skip
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
  {
    apply BigStep.if_false
    simp; all_goals assumption
  }
  {
    apply BigStep.if_true <;> assumption
  }

syntax "ass_triv" : tactic
macro_rules | `(tactic | ass_triv) => `(tactic | (assumption; try trivial))

syntax "if_tf" : tactic
macro_rules | `(tactic | if_tf) => `(tactic |  (first | apply BigStep.if_true; ass_triv | apply BigStep.if_false; ass_triv))

syntax "ite_commute" : tactic
macro_rules 
  | `(tactic| ite_commute )  => `(tactic | 
        first | (apply BigStep.if_true; ass_triv); if_tf | (apply BigStep.if_false; ass_triv); (try if_tf))

theorem commute_if: (IF b1 THEN (IF b2 THEN c11 ELSE c12) ELSE c2) 
   ~ 
   (IF b2 THEN (IF b1 THEN c11 ELSE c2) ELSE (IF b1 THEN c12 ELSE c2)) := by
  intros s t
  constructor
  intro h
  cases h with
    | if_true  _ _ _ _ _ _ hb => {
      cases hb <;> ite_commute
    }
    | if_false => {
      by_cases (beval b2 s = true) <;> ite_commute
    }

  intro h
  cases h with
    | if_true  _ _ _ _ _ _ hb => {
      cases hb <;> ite_commute
    }
    | if_false _ _ _ _ _ _ hb => {
      cases hb <;> ite_commute
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
        cases rn
        intro peq
        apply BigStep.while_false
        assumption
      }
      | while_true cond d s' t' u hcond hb hr ih_c ih_r=> {
        cases rn
        intros peq
        apply BigStep.while_true
        assumption
        rw [<-peq]
        assumption
        apply ih_r;
        rfl; assumption
      }



theorem sim_while_cong: (c ~ c') -> (WHILE b DO c) ~ (WHILE b DO c') := by
  intros eq s t
  constructor
  repeat (intro; apply sim_while_cong_aux; repeat assumption)
  intros s t
  specialize eq s t
  symm
  assumption

theorem sim_refl:  ( c ~ c ) := by
  intros
  trivial

theorem sim_sym:   ((c ~ c') <-> (c' ~ c)) := by 
  constructor
  repeat (intros h s t; symm; specialize h s t; assumption)

theorem sim_trans: ( (c ~ c') -> (c' ~ c'') -> (c ~ c'') ) := by 
  intros h1 h2 s t
  rw [h1]
  specialize h2 s t
  assumption

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
      rw [h_mid] at ht'
      apply ih'
      assumption; rfl
    | if_true _ _ _ _ _ _ _ ih =>
      cases rn
      cases h_1 with
        | if_true => apply ih; assumption; rfl
        | if_false => trivial
    | if_false cond ci ce s' t' hcond hobdy ih =>
      cases rn
      cases h_1 with
        | if_true => trivial
        | if_false => apply ih; assumption; rfl
    | while_true _ _ _ t' _ _ _ _ ih ih' => 
      cases rn
      cases h_1 with
        | while_true _ _ _ v _ _ hbody _ =>
          have h_mid : (v = t') := by
            apply ih; assumption; rfl
          rw [h_mid] at hbody
          apply ih'
          assumption
          rw [<- h_mid]
        | while_false => trivial
    | while_false =>
      cases rn; cases h_1 <;> trivial
