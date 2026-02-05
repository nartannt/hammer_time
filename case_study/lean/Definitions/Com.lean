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
notation (name := skip_term) "SKIP" => Com.skip

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

inductive SmallStep : Com × State -> Com × State -> Prop where 
  | var_assign (x a s) : SmallStep (x ::= a, s) (SKIP, s[x ↦ (aeval a s)])
  | seq_1 (c_2 s) : SmallStep (SKIP ;; c_2, s) (c_2, s)
  | seq_2 (c_1 c_1' c_2 s s') : SmallStep (c_1 , s) (c_1', s') -> SmallStep (c_1 ;; c_2, s) (c_1' ;; c_2, s')
  | if_true (b c_1 c_2 s) : beval b s -> SmallStep (IF b THEN c_1 ELSE c_2, s) (c_1, s)
  | if_false (b c_1 c_2 s) : ¬ (beval b s) -> SmallStep (IF b THEN c_1 ELSE c_2, s) (c_2, s)
  | while_loop (b c s) : SmallStep (WHILE b DO c, s) (IF b THEN c ;; WHILE b DO c ELSE SKIP, s)


inductive RTC {α : Type} : (R : α → α → Prop) -> (a : α) -> (b : α) → Prop
  | refl R a : RTC R a a
  | step (b: α) c : (R a b -> RTC R b c ->  RTC R a c)


theorem RTC_single {α : Type} {R : α → α → Prop} {a b : α} (hab : R a b) : RTC R a b := by
  apply RTC.step
  assumption
  apply RTC.refl

theorem RTC_trans {α : Type} {R : α → α → Prop} {a b c : α} (hab : RTC R a b) (hbc : RTC R b c) : RTC R a c := by
    induction hab with
      | refl => assumption
      | step _ _ _ _ ih => 
        apply RTC.step
        assumption
        apply ih
        assumption

--notation (name := small_step_judgement) init_config "->*" final_config => SmallStep init_config final_config
infixr:100 "->>" => SmallStep
infixr:100 "->*" => RTC SmallStep

def final : Com × State -> Prop  
  | cs => ¬ (exists cs', cs ->> cs')

