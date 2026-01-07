section "Small-Step Semantics of Commands"

theory Small_Step imports Star Big_Step begin

subsection "The transition relation"

inductive
  small_step :: "com * state ⇒ com * state ⇒ bool" (infix ‹→› 55)
where
Assign:  "(x ::= a, s) → (SKIP, s(x := aval a s))" |

Seq1:    "(SKIP;;c⇩2,s) → (c⇩2,s)" |
Seq2:    "(c⇩1,s) → (c⇩1',s') ⟹ (c⇩1;;c⇩2,s) → (c⇩1';;c⇩2,s')" |

IfTrue:  "bval b s ⟹ (IF b THEN c⇩1 ELSE c⇩2,s) → (c⇩1,s)" |
IfFalse: "¬bval b s ⟹ (IF b THEN c⇩1 ELSE c⇩2,s) → (c⇩2,s)" |

While:   "(WHILE b DO c,s) →
            (IF b THEN c;; WHILE b DO c ELSE SKIP,s)"


abbreviation
  small_steps :: "com * state ⇒ com * state ⇒ bool" (infix ‹→*› 55)
where "x →* y == star small_step x y"

subsection‹Executability›

code_pred small_step .

values "{(c',map t [''x'',''y'',''z'']) |c' t.
   (''x'' ::= V ''z'';; ''y'' ::= V ''x'',
    <''x'' := 3, ''y'' := 7, ''z'' := 5>) →* (c',t)}"


subsection‹Proof infrastructure›

subsubsection‹Induction rules›

text‹The default induction rule @{thm[source] small_step.induct} only works
for lemmas of the form ‹a → b ⟹ …› where ‹a› and ‹b› are
not already pairs ‹(DUMMY,DUMMY)›. We can generate a suitable variant
of @{thm[source] small_step.induct} for pairs by ``splitting'' the arguments
‹→› into pairs:›
lemmas small_step_induct = small_step.induct[split_format(complete)]


subsubsection‹Proof automation›

declare small_step.intros[simp,intro]

text‹Rule inversion:›

inductive_cases SkipE[elim!]: "(SKIP,s) → ct"
thm SkipE
inductive_cases AssignE[elim!]: "(x::=a,s) → ct"
thm AssignE
inductive_cases SeqE[elim]: "(c1;;c2,s) → ct"
thm SeqE
inductive_cases IfE[elim!]: "(IF b THEN c1 ELSE c2,s) → ct"
inductive_cases WhileE[elim]: "(WHILE b DO c, s) → ct"


text‹A simple property:›
lemma deterministic:
  "cs → cs' ⟹ cs → cs'' ⟹ cs'' = cs'"
apply(induction arbitrary: cs'' rule: small_step.induct)
apply blast+
done


subsection "Equivalence with big-step semantics"

lemma star_seq2: "(c1,s) →* (c1',s') ⟹ (c1;;c2,s) →* (c1';;c2,s')"
proof(induction rule: star_induct)
  case refl thus ?case by simp
next
  case step
  thus ?case by (metis Seq2 star.step)
qed

lemma seq_comp:
  "⟦ (c1,s1) →* (SKIP,s2); (c2,s2) →* (SKIP,s3) ⟧
   ⟹ (c1;;c2, s1) →* (SKIP,s3)"
by(blast intro: star.step star_seq2 star_trans)

text‹The following proof corresponds to one on the board where one would
show chains of ‹→› and ‹→*› steps.›

lemma big_to_small:
  "cs ⇒ t ⟹ cs →* (SKIP,t)"
proof (induction rule: big_step.induct)
  fix s show "(SKIP,s) →* (SKIP,s)" by simp
next
  fix x a s show "(x ::= a,s) →* (SKIP, s(x := aval a s))" by auto
next
  fix c1 c2 s1 s2 s3
  assume "(c1,s1) →* (SKIP,s2)" and "(c2,s2) →* (SKIP,s3)"
  thus "(c1;;c2, s1) →* (SKIP,s3)" by (rule seq_comp)
next
  fix s::state and b c0 c1 t
  assume "bval b s"
  hence "(IF b THEN c0 ELSE c1,s) → (c0,s)" by simp
  moreover assume "(c0,s) →* (SKIP,t)"
  ultimately 
  show "(IF b THEN c0 ELSE c1,s) →* (SKIP,t)" by (metis star.simps)
next
  fix s::state and b c0 c1 t
  assume "¬bval b s"
  hence "(IF b THEN c0 ELSE c1,s) → (c1,s)" by simp
  moreover assume "(c1,s) →* (SKIP,t)"
  ultimately 
  show "(IF b THEN c0 ELSE c1,s) →* (SKIP,t)" by (metis star.simps)
next
  fix b c and s::state
  assume b: "¬bval b s"
  let ?if = "IF b THEN c;; WHILE b DO c ELSE SKIP"
  have "(WHILE b DO c,s) → (?if, s)" by blast
  moreover have "(?if,s) → (SKIP, s)" by (simp add: b)
  ultimately show "(WHILE b DO c,s) →* (SKIP,s)" by(metis star.refl star.step)
next
  fix b c s s' t
  let ?w  = "WHILE b DO c"
  let ?if = "IF b THEN c;; ?w ELSE SKIP"
  assume w: "(?w,s') →* (SKIP,t)"
  assume c: "(c,s) →* (SKIP,s')"
  assume b: "bval b s"
  have "(?w,s) → (?if, s)" by blast
  moreover have "(?if, s) → (c;; ?w, s)" by (simp add: b)
  moreover have "(c;; ?w,s) →* (SKIP,t)" by(rule seq_comp[OF c w])
  ultimately show "(WHILE b DO c,s) →* (SKIP,t)" by (metis star.simps)
qed

text‹Each case of the induction can be proved automatically:›
lemma  "cs ⇒ t ⟹ cs →* (SKIP,t)"
proof (induction rule: big_step.induct)
  case Skip show ?case by blast
next
  case Assign show ?case by blast
next
  case Seq thus ?case by (blast intro: seq_comp)
next
  case IfTrue thus ?case by (blast intro: star.step)
next
  case IfFalse thus ?case by (blast intro: star.step)
next
  case WhileFalse thus ?case
    by (metis star.step star_step1 small_step.IfFalse small_step.While)
next
  case WhileTrue
  thus ?case
    by(metis While seq_comp small_step.IfTrue star.step[of small_step])
qed

lemma small1_big_continue:
  "cs → cs' ⟹ cs' ⇒ t ⟹ cs ⇒ t"
apply (induction arbitrary: t rule: small_step.induct)
apply auto
done

lemma small_to_big:
  "cs →* (SKIP,t) ⟹ cs ⇒ t"
apply (induction cs "(SKIP,t)" rule: star.induct)
apply (auto intro: small1_big_continue)
done

text ‹
  Finally, the equivalence theorem:
›
theorem big_iff_small:
  "cs ⇒ t = cs →* (SKIP,t)"
by(metis big_to_small small_to_big)


subsection "Final configurations and infinite reductions"

definition "final cs ⟷ ¬(∃cs'. cs → cs')"

lemma finalD: "final (c,s) ⟹ c = SKIP"
apply(simp add: final_def)
apply(induction c)
apply blast+
done

lemma final_iff_SKIP: "final (c,s) = (c = SKIP)"
by (metis SkipE finalD final_def)

text‹Now we can show that ‹⇒› yields a final state iff ‹→›
terminates:›

lemma big_iff_small_termination:
  "(∃t. cs ⇒ t) ⟷ (∃cs'. cs →* cs' ∧ final cs')"
by(simp add: big_iff_small final_iff_SKIP)

text‹This is the same as saying that the absence of a big step result is
equivalent with absence of a terminating small step sequence, i.e.\ with
nontermination.  Since ‹→› is determininistic, there is no difference
between may and must terminate.›

end
