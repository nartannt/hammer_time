(* Author: Gerwin Klein, Tobias Nipkow *)

subsection "Big-Step Semantics of Commands"

theory Big_Step imports Com begin

text ‹
The big-step semantics is a straight-forward inductive definition
with concrete syntax. Note that the first parameter is a tuple,
so the syntax becomes ‹(c,s) ⇒ s'›.
›

text_raw‹\snip{BigStepdef}{0}{1}{%›
inductive
  big_step :: "com × state ⇒ state ⇒ bool" (infix ‹⇒› 55)
where
Skip: "(SKIP,s) ⇒ s" |
Assign: "(x ::= a,s) ⇒ s(x := aval a s)" |
Seq: "⟦ (c⇩1,s⇩1) ⇒ s⇩2;  (c⇩2,s⇩2) ⇒ s⇩3 ⟧ ⟹ (c⇩1;;c⇩2, s⇩1) ⇒ s⇩3" |
IfTrue: "⟦ bval b s;  (c⇩1,s) ⇒ t ⟧ ⟹ (IF b THEN c⇩1 ELSE c⇩2, s) ⇒ t" |
IfFalse: "⟦ ¬bval b s;  (c⇩2,s) ⇒ t ⟧ ⟹ (IF b THEN c⇩1 ELSE c⇩2, s) ⇒ t" |
WhileFalse: "¬bval b s ⟹ (WHILE b DO c,s) ⇒ s" |
WhileTrue:
"⟦ bval b s⇩1;  (c,s⇩1) ⇒ s⇩2;  (WHILE b DO c, s⇩2) ⇒ s⇩3 ⟧ 
⟹ (WHILE b DO c, s⇩1) ⇒ s⇩3"
text_raw‹}%endsnip›

text_raw‹\snip{BigStepEx}{1}{2}{%›
schematic_goal ex: "(''x'' ::= N 5;; ''y'' ::= V ''x'', s) ⇒ ?t"
apply(rule Seq)
apply(rule Assign)
apply simp
apply(rule Assign)
done
text_raw‹}%endsnip›

thm ex[simplified]

text‹We want to execute the big-step rules:›

code_pred big_step .

text‹For inductive definitions we need command
       \texttt{values} instead of \texttt{value}.›

values "{t. (SKIP, λ_. 0) ⇒ t}"

text‹We need to translate the result state into a list
to display it.›

values "{map t [''x''] |t. (SKIP, <''x'' := 42>) ⇒ t}"

values "{map t [''x''] |t. (''x'' ::= N 2, <''x'' := 42>) ⇒ t}"

values "{map t [''x'',''y''] |t.
  (WHILE Less (V ''x'') (V ''y'') DO (''x'' ::= Plus (V ''x'') (N 5)),
   <''x'' := 0, ''y'' := 13>) ⇒ t}"


text‹Proof automation:›

text ‹The introduction rules are good for automatically
construction small program executions. The recursive cases
may require backtracking, so we declare the set as unsafe
intro rules.›
declare big_step.intros [intro]

text‹The standard induction rule 
@{thm [display] big_step.induct [no_vars]}›

thm big_step.induct

text‹
This induction schema is almost perfect for our purposes, but
our trick for reusing the tuple syntax means that the induction
schema has two parameters instead of the ‹c›, ‹s›,
and ‹s'› that we are likely to encounter. Splitting
the tuple parameter fixes this:
›
lemmas big_step_induct = big_step.induct[split_format(complete)]
thm big_step_induct
text ‹
@{thm [display] big_step_induct [no_vars]}
›


subsection "Rule inversion"

text‹What can we deduce from \<^prop>‹(SKIP,s) ⇒ t› ?
That \<^prop>‹s = t›. This is how we can automatically prove it:›

inductive_cases SkipE[elim!]: "(SKIP,s) ⇒ t"
thm SkipE

text‹This is an \emph{elimination rule}. The [elim] attribute tells auto,
blast and friends (but not simp!) to use it automatically; [elim!] means that
it is applied eagerly.

Similarly for the other commands:›

inductive_cases AssignE[elim!]: "(x ::= a,s) ⇒ t"
thm AssignE
inductive_cases SeqE[elim!]: "(c1;;c2,s1) ⇒ s3"
thm SeqE
inductive_cases IfE[elim!]: "(IF b THEN c1 ELSE c2,s) ⇒ t"
thm IfE

inductive_cases WhileE[elim]: "(WHILE b DO c,s) ⇒ t"
thm WhileE
text‹Only [elim]: [elim!] would not terminate.›

text‹An automatic example:›

lemma "(IF b THEN SKIP ELSE SKIP, s) ⇒ t ⟹ t = s"
by blast

text‹Rule inversion by hand via the ``cases'' method:›

lemma assumes "(IF b THEN SKIP ELSE SKIP, s) ⇒ t"
shows "t = s"
proof-
  from assms show ?thesis
  proof cases  ― ‹inverting assms›
    case IfTrue thm IfTrue
    thus ?thesis by blast
  next
    case IfFalse thus ?thesis by blast
  qed
qed

(* Using rule inversion to prove simplification rules: *)
lemma assign_simp:
  "(x ::= a,s) ⇒ s' ⟷ (s' = s(x := aval a s))"
  by auto

text ‹An example combining rule inversion and derivations›
lemma Seq_assoc:
  "(c1;; c2;; c3, s) ⇒ s' ⟷ (c1;; (c2;; c3), s) ⇒ s'"
proof
  assume "(c1;; c2;; c3, s) ⇒ s'"
  then obtain s1 s2 where
    c1: "(c1, s) ⇒ s1" and
    c2: "(c2, s1) ⇒ s2" and
    c3: "(c3, s2) ⇒ s'" by auto
  from c2 c3
  have "(c2;; c3, s1) ⇒ s'" by (rule Seq)
  with c1
  show "(c1;; (c2;; c3), s) ⇒ s'" by (rule Seq)
next
  ― ‹The other direction is analogous›
  assume "(c1;; (c2;; c3), s) ⇒ s'"
  thus "(c1;; c2;; c3, s) ⇒ s'" by auto
qed


subsection "Command Equivalence"

text ‹
  We call two statements ‹c› and ‹c'› equivalent wrt.\ the
  big-step semantics when \emph{‹c› started in ‹s› terminates
  in ‹s'› iff ‹c'› started in the same ‹s› also terminates
  in the same ‹s'›}. Formally:
›
text_raw‹\snip{BigStepEquiv}{0}{1}{%›
abbreviation
  equiv_c :: "com ⇒ com ⇒ bool" (infix ‹∼› 50) where
  "c ∼ c' ≡ (∀s t. (c,s) ⇒ t  =  (c',s) ⇒ t)"
text_raw‹}%endsnip›

text ‹
Warning: ‹∼› is the symbol written \verb!\ < s i m >! (without spaces).

  As an example, we show that loop unfolding is an equivalence
  transformation on programs:
›
lemma unfold_while:
  "(WHILE b DO c) ∼ (IF b THEN c;; WHILE b DO c ELSE SKIP)" (is "?w ∼ ?iw")
proof -
  ― ‹to show the equivalence, we look at the derivation tree for›
  ― ‹each side and from that construct a derivation tree for the other side›
  have "(?iw, s) ⇒ t" if assm: "(?w, s) ⇒ t" for s t
  proof -
    from assm show ?thesis
    proof cases ― ‹rule inversion on ‹(?w, s) ⇒ t››
      case WhileFalse
      thus ?thesis by blast
    next
      case WhileTrue
      from ‹bval b s› ‹(?w, s) ⇒ t› obtain s' where
        "(c, s) ⇒ s'" and "(?w, s') ⇒ t" by auto
      ― ‹now we can build a derivation tree for the \<^text>‹IF››
      ― ‹first, the body of the True-branch:›
      hence "(c;; ?w, s) ⇒ t" by (rule Seq)
      ― ‹then the whole \<^text>‹IF››
      with ‹bval b s› show ?thesis by (rule IfTrue)
    qed
  qed
  moreover
  ― ‹now the other direction:›
  have "(?w, s) ⇒ t" if assm: "(?iw, s) ⇒ t" for s t
  proof -
    from assm show ?thesis
    proof cases ― ‹rule inversion on ‹(?iw, s) ⇒ t››
      case IfFalse
      hence "s = t" by blast
      thus ?thesis using ‹¬bval b s› by blast
    next
      case IfTrue
      ― ‹and for this, only the Seq-rule is applicable:›
      from ‹(c;; ?w, s) ⇒ t› obtain s' where
        "(c, s) ⇒ s'" and "(?w, s') ⇒ t" by auto
      ― ‹with this information, we can build a derivation tree for \<^text>‹WHILE››
      with ‹bval b s› show ?thesis by (rule WhileTrue)
    qed
  qed
  ultimately
  show ?thesis by blast
qed

text ‹Luckily, such lengthy proofs are seldom necessary.  Isabelle can
prove many such facts automatically.›

lemma while_unfold:
  "(WHILE b DO c) ∼ (IF b THEN c;; WHILE b DO c ELSE SKIP)"
by blast

lemma triv_if:
  "(IF b THEN c ELSE c) ∼ c"
by blast

lemma commute_if:
  "(IF b1 THEN (IF b2 THEN c11 ELSE c12) ELSE c2) 
   ∼ 
   (IF b2 THEN (IF b1 THEN c11 ELSE c2) ELSE (IF b1 THEN c12 ELSE c2))"
by blast

lemma sim_while_cong_aux:
  "(WHILE b DO c,s) ⇒ t  ⟹ c ∼ c' ⟹  (WHILE b DO c',s) ⇒ t"
apply(induction "WHILE b DO c" s t arbitrary: b c rule: big_step_induct)
 apply blast
apply blast
done

lemma sim_while_cong: "c ∼ c' ⟹ WHILE b DO c ∼ WHILE b DO c'"
by (metis sim_while_cong_aux)

text ‹Command equivalence is an equivalence relation, i.e.\ it is
reflexive, symmetric, and transitive. Because we used an abbreviation
above, Isabelle derives this automatically.›

lemma sim_refl:  "c ∼ c" by simp
lemma sim_sym:   "(c ∼ c') = (c' ∼ c)" by auto
lemma sim_trans: "c ∼ c' ⟹ c' ∼ c'' ⟹ c ∼ c''" by auto

subsection "Execution is deterministic"

text ‹This proof is automatic.›

theorem big_step_determ: "⟦ (c,s) ⇒ t; (c,s) ⇒ u ⟧ ⟹ u = t"
  by (induction arbitrary: u rule: big_step.induct) blast+

text ‹
  This is the proof as you might present it in a lecture. The remaining
  cases are simple enough to be proved automatically:
›
text_raw‹\snip{BigStepDetLong}{0}{2}{%›
theorem
  "(c,s) ⇒ t  ⟹  (c,s) ⇒ t'  ⟹  t' = t"
proof (induction arbitrary: t' rule: big_step.induct)
  ― ‹the only interesting case, \<^text>‹WhileTrue›:›
  fix b c s s⇩1 t t'
  ― ‹The assumptions of the rule:›
  assume "bval b s" and "(c,s) ⇒ s⇩1" and "(WHILE b DO c,s⇩1) ⇒ t"
  ― ‹Ind.Hyp; note the \<^text>‹⋀› because of arbitrary:›
  assume IHc: "⋀t'. (c,s) ⇒ t' ⟹ t' = s⇩1"
  assume IHw: "⋀t'. (WHILE b DO c,s⇩1) ⇒ t' ⟹ t' = t"
  ― ‹Premise of implication:›
  assume "(WHILE b DO c,s) ⇒ t'"
  with ‹bval b s› obtain s⇩1' where
      c: "(c,s) ⇒ s⇩1'" and
      w: "(WHILE b DO c,s⇩1') ⇒ t'"
    by auto
  from c IHc have "s⇩1' = s⇩1" by blast
  with w IHw show "t' = t" by blast
qed blast+ ― ‹prove the rest automatically›
text_raw‹}%endsnip›

end


