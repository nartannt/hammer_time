theory Basic
imports Main
begin

text \<open>
Mirror of @{file "../../lean/CaseStudy/Nat/Basic.lean"}.

The Lean version proves @{text "add_zero (n : Nat) : add n 0 = n"} by
induction on @{text n}; the @{text zero} case is @{text rfl}, and the
@{text succ} case is closed by @{text hammer}. We replicate the proof
shape here so the Suc case is handed to Sledgehammer, and we use the
@{text overlord} option so Sledgehammer dumps its TPTP queries to
@{text "$ISABELLE_HOME_USER/.."} for inspection.
\<close>

sledgehammer_params [overlord, provers = zipperposition, max_facts = 5, verbose]

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc (add m n)"

text \<open>The Suc case of the induction on @{term "add n 0 = n"} — this is
the subgoal the Lean @{text hammer} call faces.\<close>

lemma add_zero_succ_case:
  assumes ih: "add n 0 = n"
  shows "add (Suc n) 0 = Suc n"
  sledgehammer
  using ih by simp

text \<open>For completeness, the original whole-lemma form.\<close>

lemma add_zero: "add n 0 = n"
  by (induction n) simp_all

end
