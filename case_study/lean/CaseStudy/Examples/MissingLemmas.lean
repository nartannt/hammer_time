import Hammer

set_option trace.auto.tptp.printQuery true
set_option trace.auto.tptp.result true
set_option hammer.preprocessingDefault "no_preprocessing"
set_option hammer.disableAesopDefault true
set_option hammer.autoPremisesDefault 100
set_option trace.hammer.premises true

inductive A : Type
inductive B : A -> Prop where
  | b x : B x 

#check B.b

example : forall x: A, B x := by
  --have h':(forall x: A, B x) := by apply B.b
  hammer [B.b] {autoPremises := 8}
