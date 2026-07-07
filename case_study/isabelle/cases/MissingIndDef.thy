theory MissingIndDef
imports Main
begin

sledgehammer_params [overlord, provers = zipperposition,
                     max_facts = 999 (* HC_MAX_FACTS *), verbose]

(* In the initial example A was a generic type, but it seems this doesn't exist in Isabelle
   similarly, prop doesn't seem to exist*)
inductive test :: "nat \<Rightarrow> bool" for n where
  constructor: "test n"

lemma lean_hammer_failure:
  shows "\<forall> x. test x"
  sledgehammer