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

example (s: State) : (("x" ::= (AExp.num 5));; ("y" ::= (AExp.var "x")), s) ==> s["x" ↦ 5]["y" ↦ 5] := by
--example (s: State) : (("x" ::= (AExp.num 5));; ("y" ::= (AExp.var "x")), s) ==> ?t := by
  apply BigStep.seq <;> apply BigStep.assign

theorem ite_skip (s: State) (t: State) (b: BExp) : (((IF b THEN Com.skip ELSE Com.skip), s) ==> t) -> t = s := by
  intro bs
  cases bs with
    | if_true  _ _ _ _ _ _ hb => cases hb; eq_refl
    | if_false _ _ _ _ _ _ hb => cases hb; eq_refl


theorem assign_sim (x: String) (a: AExp) (s: State) (s': State) :  (((x ::= a), s) ==> s' ) <-> (s' = s[x ↦ (aeval a s)]) := by
  constructor
  {
    intro h
    cases h
    eq_refl
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

set_option quotPrecheck false
notation (name := sem_equivalence) p "~" p' => forall s t, ((p, s) ==> t) = ((p', s) ==> t)

theorem unfold_while (c: Com) (b: BExp) : ((WHILE b DO c) ~ (IF b THEN c;; WHILE b DO c ELSE Com.skip)) := by
  intros s t
  let p := (WHILE b DO c)
  have hp : p = (WHILE b DO c) := by eq_refl
  let p' := (IF b THEN c;; WHILE b DO c ELSE Com.skip)
  have hp' : p' = (IF b THEN c;; WHILE b DO c ELSE Com.skip) := by eq_refl
  have h : ((p, s) ==> t) -> ((p', s) ==> t) := by
    intro h
    rw [hp] at h
    cases h with
    | while_true  _ _ _ s' t hc hb => {
      rw [hp']
      apply BigStep.if_true; assumption
      apply BigStep.seq <;>
      assumption
    }
    | while_false _ _ _  hb => {
      rw [hp']
      apply BigStep.if_false
      assumption
      apply BigStep.skip
    }

  have h' : ((p', s) ==> t) -> ((p, s) ==> t) := by
    intro h'
    rw [hp'] at h'
    rw [hp]
    cases h' with
    | if_true x y a b c hc hb =>
      {
        cases hb with
          | seq _ _ s t' u hS hT => {
            apply BigStep.while_true _ _ _ t' _ _ _ <;> assumption
          }
      }
    | if_false _ _ _ s' t hc hb =>
      {
        have h: (s = t) := by
          cases hb; eq_refl
        rw [h]
        apply BigStep.while_false; rw [h] at hc; assumption
      }
  by_cases f: ((p, s)==>t) <;>
  by_cases f': ((p', s) ==>t )
  rw [<-hp']
  rw [<-hp]
  have h: (((p, s) ==> t) = True) := by 
    sorry
  repeat sorry


