theory AddZeroSucc
imports Main
begin

sledgehammer_params [overlord, provers = zipperposition,
                     max_facts = 999 (* HC_MAX_FACTS *), verbose]

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc (add m n)"

lemma add_zero_succ_case:
  assumes ih: "add n 0 = n"
  shows "add (Suc n) 0 = Suc n"
  sledgehammer
  using ih by simp

end
