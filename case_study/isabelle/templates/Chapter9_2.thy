theory Chapter9_2
imports "HOL-IMP.Sec_Typing" "Short_Theory"
begin

text\<open>
\exercise
Reformulate the inductive predicate @{const sec_type}
as a recursive function and prove the equivalence of the two formulations:
\<close>

fun ok :: "level \<Rightarrow> com \<Rightarrow> bool" where
(* your definition/proof here *)

theorem "(l \<turnstile> c) = ok l c"
(* your definition/proof here *)

text\<open>
Try to reformulate the bottom-up system @{prop "\<turnstile> c : l"}
as a function that computes @{text l} from @{text c}. What difficulty do you face?
\endexercise

\exercise
Define a bottom-up termination insensitive security type system
@{text"\<turnstile>' c : l"} with subsumption rule:
\<close>

inductive sec_type2' :: "com \<Rightarrow> level \<Rightarrow> bool" ("(\<turnstile>'' _ : _)" [0,0] 50) where
(* your definition/proof here *)

text\<open>
Prove equivalence with the bottom-up system @{prop "\<turnstile> c : l"} without subsumption rule:
\<close>

lemma "\<turnstile> c : l \<Longrightarrow> \<turnstile>' c : l"
(* your definition/proof here *)

lemma "\<turnstile>' c : l \<Longrightarrow> \<exists>l' \<ge> l. \<turnstile> c : l'"
(* your definition/proof here *)

text\<open>
\endexercise

\exercise
Define a function that erases those parts of a command that
contain variables above some security level: \<close>

fun erase :: "level \<Rightarrow> com \<Rightarrow> com" where
(* your definition/proof here *)

text\<open>
Function @{term "erase l"} should replace all assignments to variables with
security level @{text"\<ge> l"} by @{const SKIP}.
It should also erase certain @{text IF}s and @{text WHILE}s,
depending on the security level of the boolean condition. Now show
that @{text c} and @{term "erase l c"} behave the same on the variables up
to level @{text l}: \<close>

theorem "\<lbrakk> (c,s) \<Rightarrow> s';  (erase l c,t) \<Rightarrow> t';  0 \<turnstile> c;  s = t (< l) \<rbrakk>
   \<Longrightarrow> s' = t' (< l)"
(* your definition/proof here *)

text\<open> This theorem looks remarkably like the noninterference lemma from
theory \mbox{@{short_theory "Sec_Typing"}} (although @{text"\<le>"} has been replaced by @{text"<"}).
You may want to start with that proof and modify it.
The structure should remain the same. You may also need one or
two simple additional lemmas.

In the theorem above we assume that both @{term"(c,s)"}
and @{term "(erase l c,t)"} terminate. How about the following two properties: \<close>

lemma "\<lbrakk> (c,s) \<Rightarrow> s';  0 \<turnstile> c;  s = t (< l) \<rbrakk>
  \<Longrightarrow> \<exists>t'. (erase l c, t) \<Rightarrow> t' \<and> s' = t' (< l)"
(* your definition/proof here *)


lemma "\<lbrakk> (erase l c,s) \<Rightarrow> s';  0 \<turnstile> c;  s = t (< l) \<rbrakk>
  \<Longrightarrow> \<exists>t'. (c,t) \<Rightarrow> t' \<and> s' = t' (< l)"
(* your definition/proof here *)

text\<open> Give proofs or counterexamples.
\endexercise
\<close>

end

