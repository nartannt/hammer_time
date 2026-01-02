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

notation (name := eval_state) s "[" name "↦" val "]" => state.update name val s 
notation (name := seq_semicolon) s_1 ";;" s_2 => Com.seq s_1 s_2

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
