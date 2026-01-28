import Definitions.Com
import Base.Big_Step

theorem small_step_deterministic : (cs ->> cs') -> (cs ->> cs'') -> (cs'' = cs') := by
  intros h1 h2
  induction h1 generalizing cs'' with
    | var_assign x a s=> 
      cases h2
      rfl
    | seq_1 c2 s => 
      cases h2 with
        | seq_1 => rfl
        | seq_2 _ _ _ _ _ h => cases h
    | seq_2 c1 c1' c2 s s' h ih => 
      cases h2 with
        | seq_1 => cases h
        | seq_2 _ c2' _ _ s'' h' =>
          have conf_eq: ((c1', s') = (c2', s'')) := by
            symm; apply ih; assumption
          rcases conf_eq
          rfl
    | if_true b c1 c2 s cond =>
      cases h2 with
        | if_true => rfl
        | if_false _ _ _ _ cond' =>
          rw [cond] at cond'
          trivial
    | if_false b c1 c2 s cond =>
      cases h2 with
        | if_true _ _ _ _ cond' =>
          rw [cond'] at cond
          trivial
        | if_false _ _ _ _ cond' => rfl
    | while_loop b c s =>
      cases h2; rfl


theorem small_seq_congr : ((c_1, s_1) ->* (c, s_2)) -> (c_1;;c_2, s_1) ->* (c;;c_2, s_2) := by
  intros h
  generalize rn : (c_1, s_1) = p1
  generalize rn' : (c, s_2) = p2
  rw [rn, rn'] at h
  induction h generalizing c c_1 s_1 s_2 with
    | refl => cases rn; cases rn'; apply RTC.refl
    | tail cs cs' ht hh ih =>
      cases rn; cases rn'
      rcases cs with ⟨c1', s1'⟩ 
      apply (RTC.tail (c1';;c_2, s1'))
      apply ih <;> try rfl
      apply SmallStep.seq_2
      assumption

theorem big_imp_small : (cs ==> t) -> (cs ->* (SKIP, t)) := by
  intro h
  induction h with
    | skip s =>
      apply RTC.refl
    | assign =>
      apply RTC_single
      apply SmallStep.var_assign
    | seq c1 c2 s t u h1 h2 ih ih' =>
      have h_mid_1 : ((c1;;c2, s) ->* (SKIP;;c2, t)) := by
        apply small_seq_congr
        assumption
      have h_mid_2 : ((SKIP;;c2, t) ->* (c2, t)) := by
        apply RTC_single
        apply SmallStep.seq_1
      repeat (apply RTC_trans; assumption)
      apply RTC.refl
    | if_true b c c' s t hcond hb ih =>
      have h: (RTC SmallStep (IF b THEN c ELSE c', s) (c, s)) := by
        apply RTC_single
        apply SmallStep.if_true
        assumption
      apply RTC_trans <;> assumption
    | if_false b c c' s t hcond hb ih =>
      have h: (RTC SmallStep (IF b THEN c ELSE c', s) (c', s)) := by
        apply RTC_single
        apply SmallStep.if_false
        assumption
      apply RTC_trans <;> assumption
    | while_false cond d s' hcond => {
      apply (RTC.tail (IF cond THEN d;;WHILE cond DO d ELSE SKIP, s'))
      apply RTC_single
      apply SmallStep.while_loop
      apply SmallStep.if_false
      assumption
    }
    | while_true cond d s' t' u hcond hb hr ih_c ih_r => {
      have h1: (RTC SmallStep (WHILE cond DO d, s') (d;;WHILE cond DO d, s')) := by
        have h2: (RTC SmallStep (WHILE cond DO d, s') (IF cond THEN d;;WHILE cond DO d ELSE SKIP, s')) := by
          apply RTC_single
          apply SmallStep.while_loop
        apply RTC_trans
        assumption
        apply RTC_single
        apply SmallStep.if_true
        assumption

      have h3: (RTC SmallStep (d;;WHILE cond DO d, s') (SKIP;;WHILE cond DO d, t') ) := by
        apply small_seq_congr
        assumption

      have h4: (RTC SmallStep (SKIP;;WHILE cond DO d, t') (WHILE cond DO d, t') ) := by
        apply RTC_single
        apply SmallStep.seq_1

      repeat (apply RTC_trans; assumption)
      apply RTC.refl
    }


