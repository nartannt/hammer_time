import Hammer

set_option trace.auto.tptp.printQuery true
set_option trace.auto.tptp.result true
set_option hammer.preprocessingDefault "no_preprocessing"
set_option hammer.disableAesopDefault true
set_option hammer.autoPremisesDefault 16
set_option trace.hammer.premises true


def zero : Nat := 0
def one : Nat := Nat.succ zero
def two : Nat := Nat.succ one
def three : Nat := Nat.succ two

--theorem three_is_three : three = Nat.succ (Nat.succ (Nat.succ 0)) := by
--  hammer [] {autoPremises := 0}
--
--theorem zero_is_not_one : 0 = Nat.succ 0 -> False := by
--  hammer [] {autoPremises := 16}

theorem one_is_not_zero : zero = one -> False := by
  hammer [] {autoPremises := 4}

theorem one_is_not_two : one = two -> False := by
  -- this fails
  --try hammer [] {autoPremises := 16}
  -- this fails if the number of premises is less than 35 (succeeds modulo kernel error)
  hammer [two, one, zero, one_is_not_zero] {autoPremises := 35}

--theorem no_eq_three_is_not_two : Nat.succ (Nat.succ (Nat.succ 0)) = Nat.succ (Nat.succ 0) -> False := by
   -- succeeds instantly
--   hammer

theorem three_is_not_two : three = two -> False := by
  -- this fails
  --try hammer [] {autoPremises := 16}
  -- minimised premises and autoPremises number
  hammer [
     three, 
     one_is_not_two, 
     Nat.Linear.ExprCnstr.eq_true_of_isValid,
     Nat.lt_add_one,
     Array.getElem_map,
     Nat.one_and_eq_mod_two,
     of_decide_eq_true,
     Subsingleton.elim,
     Nat.instNeZeroSucc,
     instSubsingletonDecidable,
     ite_cond_eq_true,
     Function.Injective.eq_iff,
     of_decide_eq_false,
     bne_self_eq_false ] {autoPremises := 21}


