import Hammer

-- Print TPTP output
set_option trace.auto.tptp.printQuery true

-- use mepo for library suggestions
open Lean LibrarySuggestions in
set_library_suggestions mepoSelector (useRarity := false)

namespace Hammer.CaseStudy.NaturalN

open Nat

def add : Nat → Nat → Nat
| 0, n => n
| succ m, n => succ (add m n)

theorem add_zero (n : Nat) : add n 0 = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    sorry
    -- hammer

theorem add_assoc (m n p : Nat) : add (add m n) p = add m (add n p) := by
  induction m with
  | zero => rfl
  | succ m ih => simp [add, ih]

theorem add_succ (n m : Nat) : add n (succ m) = succ (add n m) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [add, ih]

theorem add_comm (m n : Nat) : add m n = add n m := by
  induction m with
  | zero => simp [add, add_zero]
  | succ m ih =>
    sorry
    -- simp [add, ih, add_succ]

def double : Nat → Nat
| 0 => 0
| succ n => succ (succ (double n))

theorem double_add (m : Nat) : double m = add m m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    sorry
    -- simp [double, add, ih, add_succ]

end Hammer.CaseStudy.NaturalN
