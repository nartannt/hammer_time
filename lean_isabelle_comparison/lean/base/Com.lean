
inductive AExp : Type where
| num : Z → AExp
| var : String → AExp
| add : AExp → AExp → AExp

inductive BExp : Type where
  | bc {B} : B -> BExp
  | not : BExp -> BExp
  | and : BExp -> BExp -> BExp
  | less : AExp -> AExp -> BExp

inductive Com : Type where
| skip : Com
| assign : String → AExp → Com
| seq : Com → Com → Com
| ite : BExp → Com → Com → Com
| while : BExp → Com → Com
