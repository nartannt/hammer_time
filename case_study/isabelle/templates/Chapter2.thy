theory Chapter2
imports Main
begin

text\<open>
\section*{Chapter 2}

\exercise
Use the \textbf{value} command to evaluate the following expressions:
\<close>

 "1 + (2::nat)"
 "1 + (2::int)"
 "1 - (2::nat)"
 "1 - (2::int)"
 "[a,b] @ [c,d]"

text\<open>
\endexercise


\exercise
Recall the definition of our own addition function on @{typ nat}:
\<close>

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc(add m n)"

text\<open>
Prove that @{const add} is associative and commutative.
You will need additional lemmas.
\<close>

lemma add_assoc: "add (add m n) p = add m (add n p)"
(* your definition/proof here *)

lemma add_comm: "add m n = add n m"
(* your definition/proof here *)

text\<open> Define a recursive function \<close>

fun double :: "nat \<Rightarrow> nat" where
(* your definition/proof here *)

text\<open> and prove that \<close>

lemma double_add: "double m = add m m"
(* your definition/proof here *)
text\<open>
\endexercise


\exercise
Define a function that counts the number of occurrences of
an element in a list:
\<close>

fun count :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
(* your definition/proof here *)
text \<open>
Test your definition of @{term count} on some examples.
Prove the following inequality:
\<close>

theorem "count xs x \<le> length xs"
(* your definition/proof here *)

text\<open>
\endexercise


\exercise
Define a function @{text snoc} that appends an element to the end of a list.
Do not use the existing append operator @{text "@"} for lists.
\<close>

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
(* your definition/proof here *)

text \<open>
Convince yourself on some test cases that your definition
of @{term snoc} behaves as expected.
With the help of @{text snoc} define a recursive function @{text reverse}
that reverses a list. Do not use the predefined function @{const rev}.
\<close>

fun reverse :: "'a list \<Rightarrow> 'a list" where
(* your definition/proof here *)

text \<open>
Prove the following theorem. You will need an additional lemma.
\<close>
theorem "reverse (reverse xs) = xs"
(* your definition/proof here *)

text\<open>
\endexercise


\exercise
The aim of this exercise is to prove the summation formula
\[ \sum_{i=0}^{n}i = \frac{n(n+1)}{2} \]
Define a recursive function @{text "sum_upto n = 0 + ... + n"}:
\<close>

fun sum_upto :: "nat \<Rightarrow> nat" where
(* your definition/proof here *)

text \<open>
Now prove the summation formula by induction on @{text "n"}.
First, write a clear but informal proof by hand following the examples
in the main text. Then prove the same property in Isabelle:
\<close>

lemma "sum_upto n = n * (n+1) div 2"
(* your definition/proof here *)

text\<open>
\endexercise


\exercise
Starting from the type @{text "'a tree"} defined in the text, define
a function that collects all values in a tree in a list, in any order,
without removing duplicates.
\<close>
datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun contents :: "'a tree \<Rightarrow> 'a list" where
(* your definition/proof here *)

text\<open>
Then define a function that sums up all values in a tree of natural numbers
\<close>

fun sum_tree :: "nat tree \<Rightarrow> nat" where
(* your definition/proof here *)

text\<open> and prove \<close>

lemma "sum_tree t = sum_list(contents t)"
(* your definition/proof here *)

text\<open>
\endexercise

\exercise
Define a new type @{text "'a tree2"} of binary trees where values are also
stored in the leaves of the tree.  Also reformulate the
@{text mirror} function accordingly. Define two functions \<close>

fun pre_order :: "'a tree2 \<Rightarrow> 'a list" where
(* your definition/proof here *)

fun post_order :: "'a tree2 \<Rightarrow> 'a list" where
(* your definition/proof here *)

text\<open>
that traverse a tree and collect all stored values in the respective order in a list. Prove \<close>

lemma "pre_order (mirror t) = rev (post_order t)"
(* your definition/proof here *)

text\<open>
\endexercise

\exercise
Define a recursive function
\<close>

fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
(* your definition/proof here *)

text\<open>
such that @{text "intersperse a [x\<^sub>1, ..., x\<^sub>n] = [x\<^sub>1, a, x\<^sub>2, a, ..., a, x\<^sub>n]"}.
Prove
\<close>

lemma "map f (intersperse a xs) = intersperse (f a) (map f xs)"
(* your definition/proof here *)

text\<open>
\endexercise


\exercise
Write a tail-recursive variant of the @{text add} function on @{typ nat}:
\<close>

fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
(* your definition/proof here *)

text\<open>
Tail-recursive means that in the recursive case, @{const itadd} needs to call
itself directly: \mbox{@{term"itadd (Suc m) n"}} @{text"= itadd \<dots>"}.
Prove
\<close>

lemma "itadd m n = add m n"
(* your definition/proof here *)

text\<open>
\endexercise


\exercise\label{exe:tree0}
Define a datatype @{text tree0} of binary tree skeletons which do not store
any information, neither in the inner nodes nor in the leaves.
Define a function that counts the number of all nodes (inner nodes and leaves)
in such a tree:
\<close>

fun nodes :: "tree0 \<Rightarrow> nat" where
(* your definition/proof here *)

text \<open>
Consider the following recursive function:
\<close>

fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
"explode 0 t = t" |
"explode (Suc n) t = explode n (Node t t)"

text \<open>
Experiment how @{text explode} influences the size of a binary tree
and find an equation expressing the size of a tree after exploding it
(\noquotes{@{term [source] "nodes (explode n t)"}}) as a function
of @{term "nodes t"} and @{text n}. Prove your equation.
You may use the usual arithmetic operations including the exponentiation
operator \<open>\<close>@{text"^"}''. For example, \noquotes{@{prop [source] "2 ^ 2 = 4"}}.

Hint: simplifying with the list of theorems @{thm[source] algebra_simps}
takes care of common algebraic properties of the arithmetic operators.
\endexercise
\<close>

text\<open>

\exercise
Define arithmetic expressions in one variable over integers (type @{typ int})
as a data type:
\<close>

datatype exp = Var | Const int | Add exp exp | Mult exp exp

text\<open>
Define a function @{text eval} that evaluates an expression at some value:
\<close>

fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
(* your definition/proof here *)

text\<open>
For example, @{prop"eval (Add (Mult (Const 2) Var) (Const 3)) i = 2*i+3"}.

A polynomial can be represented as a list of coefficients, starting with
the constant. For example, @{term "[4, 2, -1, 3::int]"} represents the
polynomial $4 + 2x - x^2 + 3x^3$.
Define a function @{text evalp} that evaluates a polynomial at a given value:
\<close>

fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
(* your definition/proof here *)

text\<open>
Define a function @{text coeffs} that transforms an expression into a polynomial.
This will require auxiliary functions.
\<close>

fun coeffs :: "exp \<Rightarrow> int list" where
(* your definition/proof here *)

text\<open>
Prove that @{text coeffs} preserves the value of the expression:
\<close>

theorem evalp_coeffs: "evalp (coeffs e) x = eval e x"
(* your definition/proof here *)

text\<open>
Hint: consider the hint in Exercise~\ref{exe:tree0}.
\endexercise
\<close>

end

