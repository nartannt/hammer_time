import Hammer

namespace HammerCases.AddZeroSucc

def add2 : Nat → Nat → Nat
  | 0, n => n
  | .succ m, n => .succ (add2 m n)

theorem add_zero (n : Nat) : add2 n 0 = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    hammer

theorem add_zero_succ (n : Nat) (ih : add2 n 0 = n) :
    add2 (n + 1) 0 = n + 1 := by
  hammer

end HammerCases.AddZeroSucc
