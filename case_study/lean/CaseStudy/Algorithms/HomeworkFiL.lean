import CaseStudy.Algorithms.HomeworkFiLDefs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.List.Sort
import Mathlib.Data.Tree.Basic
import Mathlib.Tactic
import Mathlib.Data.List.TakeWhile

/- # Homework 4 : Algorithms
Name :

The exercices from this sheet are taken from *Functional Data Structures and Algorithms*
by Nipkow.

The reference is available online and should be consulted if
you feel like you are missing context.
The exercice numbers refer to the ones from the book.

**Important:** Make sure to follow the instructions given in the exercise. -/

variable {α : Type*}

section select
variable [LinearOrder α] [Inhabited α]
open List

/- ## Exercise 2.1
Consider the two following measure of complexity on insertion sort: -/
#check List.insertionSort

def time_orderedInsert : α → List α → ℕ
| _, [] => 1
| x, (y :: ys) => (if x ≤ y then 0 else time_orderedInsert x ys) + 1

def time_insort :  List α → ℕ
| [] => 1
| (x :: xs) =>
    time_insort xs + time_orderedInsert x (xs.insertionSort (· ≤ ·)) + 1
/-
Show that `time_insort` achieves its optimal value of `2n + 1` for sorted
lists, and its worst-case value of `(n + 1)(n + 2) / 2 ` for the list `(range' 1 n).reverse`.

For the worst case, you might find it worth while to prove some lemmas beforehand. -/

#reduce (range' 1 5).reverse
#reduce time_insort (range' 1 20)
#reduce time_insort (range' 1 20).reverse

example {l : List α} (h : l.Pairwise (· ≤ ·)) : time_insort l = 2 * l.length + 1 := by
  induction l
  · aesop
  · aesop (add norm time_insort)
    have : time_orderedInsert head (List.insertionSort (fun x x_1 ↦ x ≤ x_1) tail) = 1 := by
      clear tail_ih
      induction tail
      · aesop
      · rename_i head_1 tail tail_ih
        simp_all only [List.mem_cons, or_true, implies_true, true_implies, forall_eq_or_imp]
        obtain ⟨left, _⟩ := left
        rw [List.Pairwise.insertionSort_eq right]
        aesop (add norm time_orderedInsert)
    aesop

/- Unnec.-/
lemma List.insort_iota_cons (n : ℕ) :
    (List.insertionSort (· ≤ ·) ((n + 1) :: (range' 1 n).reverse)) =
    (List.insertionSort (· ≤ ·) (range' 1 n).reverse) ++ [n+1] := by
  rw [List.insertionSort_cons_eq_take_drop]
  have h1 : List.takeWhile (decide ¬n + 1 ≤ ·) (List.insertionSort (· ≤ ·) (range' 1 n).reverse)
    = (List.insertionSort (· ≤ ·) (range' 1 n).reverse) := by
    simp only [not_le, takeWhile_eq_self_iff, decide_eq_true_eq]
    aesop (add unsafe tactic (by grind))
  have : List.dropWhile (decide ¬n + 1 ≤ ·) (List.insertionSort (· ≤ ·) (range' 1 n).reverse)
    = [] := by
    simp only [not_le, List.dropWhile_eq_nil_iff, decide_eq_true_eq]
    aesop
  rw [h1, this]

lemma List.insort_iota (n : ℕ) : (insertionSort (· ≤ · : ℕ → ℕ → Prop) (range' 1 n).reverse) =
   range' 1 n := by
  apply List.Perm.eq_of_pairwise' (r := (· ≤ · : ℕ → ℕ → Prop)) (List.pairwise_insertionSort ..)
    pairwise_le_range'
  exact Perm.trans (perm_insertionSort (· ≤ ·) _) (reverse_perm _)

omit [Inhabited α] in
lemma List.time_orderedInsert_eq_len_iff (a : α) (l : List α) (ha : ∀ b ∈ l, b < a) :
    time_orderedInsert a l = l.length + 1 := by
  induction l
  · aesop
  aesop (add norm time_orderedInsert)

lemma List.range'_succ_range {n : ℕ} :
    (range' 1 (n + 1)).reverse = (n + 1) :: (range' 1 n).reverse := by
  rw [reverse_eq_cons_iff, range'_1_concat]
  grind

example (n : ℕ) : time_insort (range' 1 n).reverse = (n + 1) * (n + 2) / 2 := by
  induction n with
  | zero => aesop
  | succ n _ =>
    have : time_orderedInsert (n + 1) ((range' 1 n).reverse.insertionSort (· ≤ ·)) = n + 1 := by
      simp only [insort_iota] at *
      rw [time_orderedInsert_eq_len_iff]
      · simp only [length_range']
      · aesop (add norm add_comm)
    unfold time_insort
    rw [List.range'_succ_range]
    grind


/- ## Exercise 3.1 (*)
Recall the notion of **selection**:

Given a list `xs` of length `n` with some linear order defined on its elements
and a natural number `k < n`, return the `k`-th smallest number in the list
(starting with `k = 0` for the minimal element).

A simple special case of selection is `select 0 xs`, i.e. the minimum.
Implement a linear-time function `select0` such that
`xs ≠ [] → select0 xs = select 0 xs`
and prove this. This function should be tail-recursive and traverse the list exactly
once. You need not prove the linear running time. (it should be obvious)

For your proof, you might find it worth while to spend time proving some
obvious lemmas about `select0`. -/

def List.select0Aux (a : α) : List α → α
| .nil => a
| .cons x xs => if x < a then select0Aux x xs else select0Aux a xs

def List.select0 : List α → α
| .nil => panicWithPosWithDecl "" "List.select0" 28 18 "List is empty"
| .cons x xs => select0Aux x xs

#eval [2,4,3,1,4].select0

lemma List.select0_le_head' (xs : List α) (a : α) : List.select0 (a :: xs) ≤ a := by
  induction xs generalizing a
  · rfl
  · rename_i head' tail tail_ih
    simp_all only [select0, select0Aux]
    split
    next h =>
      obtain tail_ih := tail_ih head'
      apply (lt_of_le_of_lt tail_ih h).le
    next h => simp_all only [not_lt]

lemma List.select0Aux_le_head (xs : List α) (a : α) : List.select0Aux a xs ≤ a :=
  select0_le_head' _ _

lemma List.select0_le_of_le_head {a b : α} (xs : List α) (h : a ≤ b) :
    List.select0 (a :: xs) ≤ List.select0 (b :: xs) := by
  simp_all only [select0]
  induction xs generalizing a b <;> aesop (add norm List.select0Aux, forward safe [lt_of_lt_of_le])

lemma List.select0Aux_of_select0Aux (a : α) (l : List α) :
    select0Aux (select0Aux a l) l = select0Aux a l := by
  induction l generalizing a <;>
    aesop (add norm select0Aux, forward safe [List.select0Aux_le_head, lt_of_lt_of_le])

lemma List.select0Aux_eq_head_iff_head_le_mem (a : α) (l : List α) :
    List.select0Aux a l = a ↔ ∀ b ∈ l, a ≤ b := by
  constructor
  · intro ha b hb
    induction l <;>
      -- set_option aesop.dev.statefulForward false in
      -- set_option trace.profiler true in
      aesop (add norm [select0Aux, List.select0Aux_le_head],
        forward unsafe select0Aux_of_select0Aux)
  · intro haleb
    induction l <;> aesop (add norm select0Aux)

lemma List.select0Aux_le_mem (a : α) (l : List α) :
    ∀ b ∈ l, List.select0Aux a l ≤ b := by
  intro b ha
  induction l generalizing a <;>
    aesop (add norm select0Aux, unsafe forward List.select0Aux_le_head, unsafe forward le_trans)

lemma List.select0_mem_self {l : List α} (h : l ≠ []) : l.select0 ∈ l := by
  induction l
  · simp at h
  · aesop (add norm [List.select0, List.select0Aux])
    · left
      rw [List.select0Aux_eq_head_iff_head_le_mem] at *
      exact fun b hb ↦ le_trans h_1 (h b hb)
    by_cases h_le : head ≤ List.select0Aux x_1 xs
    · left
      rw [List.select0Aux_eq_head_iff_head_le_mem]
      exact fun b hb ↦ (le_trans h_le (List.select0Aux_le_mem _ _ b hb))
    simp_all only [not_le]
    induction xs generalizing head x_1
    · aesop
    · aesop (add norm List.select0Aux, safe forward [lt_of_le_of_lt, le_trans])
      · replace tail_ih := tail_ih head head_1 h_3 h_1 h_le
        aesop
      · replace tail_ih := tail_ih head x_1 h_3 h h_le
        aesop

example {xs : List α} (h : xs ≠ []) : List.select0 xs = List.select 0 xs := by
  obtain hk := List.length_pos_of_ne_nil h
  apply select_unique hk _ (select_prop1 hk) _ (select_prop2 hk)
  · have : List.filter (fun x ↦ decide (x < xs.select0)) xs = [] := by
      simp only [filter_eq_nil_iff, decide_eq_true_eq, not_lt]
      intro a ha
      induction xs
      · aesop
      · aesop (add apply safe [List.select0_le_head'])
        aesop (add norm [List.select0, List.select0Aux]) <;>
          exact le_trans (List.select0_le_of_le_head xs h) tail_ih
    simp_all only [ne_eq, nonpos_iff_eq_zero, List.length_eq_zero_iff]
  · nth_rw 2 [List.length_eq_length_filter_add (xs.select0 < ·)]
    simp_all only [tsub_zero, lt_add_iff_pos_right, ← List.countP_eq_length_filter, List.countP_pos_iff]
    use xs.select0
    simp [List.select0_mem_self h]

end select
/- ## Exercise 4.1.
Recall the function `inorder` from the lecture and the notes.
It has quadratic complexity because the running time
of `++` is linear in the length of its first argument.
Define a function `inorder2 : Tree α → List α → List α` that avoids
`++` but accumulates the result in its second parameter
via `::` only. Its running time should be linear in the size of the tree.
Prove `inorder2 t xs = inorder t ++ xs`. -/

def inorder2 : Tree α → List α → List α
| Tree.nil => fun xs => xs
| Tree.node x l r => fun xs => inorder2 l (x :: inorder2 r xs)

example (t : Tree α) (xs : List α) : inorder2 t xs = (inorder t) ++ xs := by
  induction t generalizing xs <;> aesop (add norm [inorder2, inorder])

/- ## Exercise 4.2. (*)
Write a function `enum_tree : List α → List (Tree α)` such that
`Set (enum_tree xs) = {t | inorder t = xs}` and prove this proposition. You could
also prove that `enum_tree` produces lists of distinct elements, although that
is likely to be harder. -/

-- **Note** : WIP

def add_children_aux_r (col : List (Tree α)) (a : α) (xr : List (Tree α)) :
    List (Tree α) :=
    match xr with
    | List.nil => col
    | List.cons r xr => add_children_aux_r (Tree.node a Tree.nil r :: col) a xr

def add_children_aux_l (col : List (Tree α)) (a : α) (xl : List (Tree α)) :
    List (Tree α) :=
  match xl with
  | List.nil => col
  | List.cons l xl => add_children_aux_l (Tree.node a l Tree.nil :: col) a xl

def add_children_aux_lr (col : List (Tree α)) (a : α) (xl : List (Tree α)) (xr : List (Tree α)) :
    List (Tree α) :=
  match xl with
  | List.nil => col
  | List.cons l xl =>
    match xr with
    | List.nil => col
    | List.cons r xr => add_children_aux_lr (Tree.node a l r :: col) a xl (r :: xr)

def add_children (a : α) (xl : List (Tree α)) (xr : List (Tree α)) : List (Tree α) :=
  match xl with
  | List.nil =>
    match xr with
    | List.nil => [Tree.node a Tree.nil Tree.nil]
    | List.cons r xr => add_children_aux_r [] a (r :: xr)
  | List.cons l xl =>
    match xr with
    | List.nil => add_children_aux_l [] a (l :: xl)
    | List.cons r xr => add_children_aux_lr [] a (l :: xl) (r :: xr)

#eval add_children 1 [] []
#eval add_children 1 [Tree.node 2 Tree.nil Tree.nil, Tree.node 3 Tree.nil Tree.nil]
  [Tree.node 4 Tree.nil Tree.nil]
#eval add_children 1 [] [Tree.node 3 Tree.nil Tree.nil]

partial def enum_tree_aux (past : List α) (col : List (Tree α)) (xs : List α) : List (Tree α) :=
  match xs with
  | List.nil => []
  | List.cons a xs => (add_children a (enum_tree_aux past [] []) (enum_tree_aux [] [] xs))
    ++ enum_tree_aux (a :: past) [] xs

def enum_tree (xs : List α) : List (Tree α) :=
  enum_tree_aux [] [] xs

#eval enum_tree_aux [] [] [1,2]


/- ## Exercise 4.3.1 (**)
Although we focus on binary trees, arbitrarily branching trees can be
defined just as easily: -/
inductive RTree (α : Type*)
| node : α → List (RTree α) → RTree α

open RTree
/-
Such trees are often called rose trees. They are a case of what we call "Nested recursion".
The goal of this exercise is to define the following
`mir : RTree α →  RTree α` that mirrors a rose tree and to prove `mir (mir t) = t`.

The section on nested recursion of this blog post will probably be of help for the
defition of `mir`:
https://lean-lang.org/blog/2024-1-11-recursive-definitions-in-lean/

For your proof, I suggest creating your own induction principle first. -/

def RTree.mir : RTree α → RTree α
| node x xs => node x (xs.reverse.map (·.mir))

@[induction_eliminator]
def RTree.induction_principle
  (p : RTree α → Prop)
  (node : (x : α) → (ts : List (RTree α)) → (ih : ∀ t ∈ ts, p t) → p (node x ts))
  : ∀ t : RTree α, p t :=
  @RTree.rec α
    p
    (λ ts => ∀ t ∈ ts, p t)
    node
    (List.forall_mem_nil p)
    (λ _ _ h_head h_tail => List.forall_mem_cons.mpr (And.intro h_head h_tail))

theorem RTree.mir_mir (r : RTree α) : r.mir.mir = r := by
  induction' r with x xs ih1
  induction' xs with y ys ih2
  · simp [mir]
  · simp [mir]
    refine ⟨ih1 y (List.mem_cons_self), ?_⟩
    simp [mir] at ih2
    apply ih2
    intro t ht
    exact ih1 t (List.mem_cons_of_mem y ht)

/- ## Exercice 4.3.2 (*)
Now define a height function `RTree.height` and show
`height_lt {a : α} {t : RTree α} {ts : List (RTree α)} : t ∈ ts → height t < height (node a ts)`

Use this to specify the termination proof in `mir` using `termination_by t => t.height`. -/

def WithBot.toZero (x : WithBot ℕ ) : ℕ :=
  match x with
  | ⊥ => 0
  | (x : ℕ) => x

def RTree.height : RTree α → ℕ
| RTree.node _ ts => 1 + (ts.map (fun x => height x)).maximum.toZero

theorem height_lt {a : α} {t : RTree α} {ts : List (RTree α)} :
    t ∈ ts → height t < height (node a ts) := by
  intro h
  simp_rw [height, WithBot.toZero]
  split
  next x heq =>
    rw [WithBot.none_eq_bot] at heq
    simp_all
  next x x_1 heq =>
    rw [WithBot.some_eq_coe x_1] at heq
    rw [List.maximum_eq_coe_iff] at heq
    · obtain ⟨ha, hb⟩ := heq
      simp at hb
      linarith only [hb _ h]

def RTree.mir' : RTree α → RTree α
| node x xs => node x (List.map (fun ⟨t, _⟩ => t.mir') xs.attach.reverse)
termination_by t => t.height
decreasing_by exact height_lt (by assumption)
