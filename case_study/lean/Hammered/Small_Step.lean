import Definitions.Com
import Hammered.Big_Step
import Hammer

theorem small_step_deterministic : (cs ->> cs') -> (cs ->> cs'') -> (cs'' = cs') := by
  intros h1 h2
  induction h1 generalizing cs'' with
    | var_assign x a s => 
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
  induction h generalizing c c_1 s_1 c_2 s_2 with
    | refl => cases rn; cases rn'; apply RTC.refl
    | step cs cs' ht hh ih =>
      cases rn; cases rn'
      rcases cs with ⟨c_1', s_1'⟩ 
      have h: (RTC SmallStep (c_1';;c_2, s_1') (c;;c_2, s_2)) := by
        apply ih <;> rfl

      have h': (RTC SmallStep (c_1;;c_2, s_1) (c_1';;c_2, s_1')) := by
        apply RTC.step
        apply SmallStep.seq_2
        assumption
        apply RTC.refl

      hammer


theorem big_imp_small : (cs ==> t) -> (cs ->* (SKIP, t)) := by
  intro h
  induction h with
    | skip s =>
      apply RTC.refl
    | assign =>
      try hammer
      try hammer [RTC_single]
      try hammer [SmallStep.var_assign]
      --hammer [RTC_single, SmallStep.var_assign]
    | seq c1 c2 s t u h1 h2 ih ih' =>
      try hammer
      try hammer [small_seq_congr, RTC_single, SmallStep.seq_1, RTC_trans, RTC.refl]
      have h_mid_1 : ((c1;;c2, s) ->* (SKIP;;c2, t)) := by
        hammer
      have h_mid_2 : ((SKIP;;c2, t) ->* (c2, t)) := by
        try hammer
        hammer [SmallStep.seq_1]
      try hammer [RTC_trans]
      repeat (apply RTC_trans; assumption)
      apply RTC.refl
    | if_true b c c' s t hcond hb ih =>
      have h: (RTC SmallStep (IF b THEN c ELSE c', s) (c, s)) := by
        hammer [SmallStep.if_true]
      hammer
    | if_false b c c' s t hcond hb ih =>
      have h: (RTC SmallStep (IF b THEN c ELSE c', s) (c', s)) := by
        hammer [SmallStep.if_false]
      hammer
    | while_false cond d s' hcond => {
      hammer [RTC.step, SmallStep.while_loop, RTC_single, SmallStep.if_false]
    }
    | while_true cond d s' t' u hcond hb hr ih_c ih_r => {
      have h1: (RTC SmallStep (WHILE cond DO d, s') (d;;WHILE cond DO d, s')) := by
        have h2: (RTC SmallStep (WHILE cond DO d, s') (IF cond THEN d;;WHILE cond DO d ELSE SKIP, s')) := by
          hammer [SmallStep.while_loop, SmallStep.if_true]
        apply RTC_trans
        assumption
        apply RTC_single
        apply SmallStep.if_true
        assumption

      have h3: (RTC SmallStep (d;;WHILE cond DO d, s') (SKIP;;WHILE cond DO d, t') ) := by
        hammer

      have h4: (RTC SmallStep (SKIP;;WHILE cond DO d, t') (WHILE cond DO d, t') ) := by
        hammer [SmallStep.seq_1]

      repeat (apply RTC_trans; assumption)
      apply RTC.refl
    }

theorem step_sem_imp : (cs ->> cs') -> (cs' ==> t) -> (cs ==> t) := by
  intros h h'
  try induction h generalizing t <;> hammer [BigStep.assign, BigStep.skip, BigStep.seq, BigStep.if_true, BigStep.if_false, BigStep.while_true, BigStep.while_false, unfold_while]
  induction h generalizing t with
    | var_assign =>
      cases h'
      apply BigStep.assign
    | seq_1 =>
      apply BigStep.seq
      apply BigStep.skip
      assumption
    | seq_2 c1 c1' c2 s s' h'' ih =>
      cases h' with
        | seq _ _ _ t' _ hl hr =>
          apply BigStep.seq
          apply ih
          assumption
          assumption
    | if_true =>
      apply BigStep.if_true <;>
      assumption
    | if_false => 
      apply BigStep.if_false <;>
      assumption
    | while_loop =>
      rw [unfold_while]
      assumption

theorem small_imp_big : (cs ->* (SKIP, t)) -> (cs ==> t) := by
  intro h
  generalize rn : (SKIP, t) = p
  rw [rn] at h
  induction h generalizing t with
    | refl =>
      cases rn
      apply BigStep.skip
    | step cs' cs'' hh ht ih =>
      rcases cs' with ⟨c_1', s_1'⟩ 
      cases rn
      simp at ih
      apply step_sem_imp <;>
      assumption


theorem small_big_eq : ((c, s) ==> t) <-> ((c, s) ->* (SKIP, t) ) := by
  hammer

theorem small_final : final (c, s) <-> (c = SKIP) := by
  constructor
  {
    intro h
    induction c with
      | skip =>
        rfl
      | assign var val =>
        exfalso
        apply h
        exists (SKIP, s[var ↦ (aeval val s)])
        apply SmallStep.var_assign
      | seq c c' ih ih' =>
        exfalso
        apply h
        by_cases h'': (final (c, s))
        have hc : (c = SKIP) := by
          apply ih; assumption
        cases hc
        exists (c', s)
        apply SmallStep.seq_1
        simp [final] at h''
        cases h'' with | intro d h''
        cases h'' with | intro t h''
        try hammer [SmallStep.seq_1, SmallStep.seq_2]
        exists (d;;c', t)
        apply SmallStep.seq_2
        assumption
      | ite cond ci ce ih ih' =>
        try hammer [SmallStep.if_true, SmallStep.if_false]
        exfalso
        apply h
        by_cases hcond:(beval cond s = true)
        exists (ci, s)
        apply SmallStep.if_true
        assumption
        exists (ce, s)
        apply SmallStep.if_false
        assumption
      | «while» cond loop ih=>
        exfalso
        apply h
        exists (IF cond THEN loop ;; WHILE cond DO loop ELSE SKIP, s)
        apply SmallStep.while_loop
  }
  {
    intro h; cases h
    unfold final
    intros cs h'
    cases h' with | intro cs' h'
    simp [cs] at h'
    cases h'
  }

theorem big_step_small_step_termination : (exists t, cs ==> t) <-> (exists cs', cs ->* cs' ∧ final cs') := by
  constructor
  {
    --try hammer
    --try hammer [small_big_eq, small_final]
    intro h
    cases h with | intro t h
    exists (SKIP, t)
    constructor
    rw [<- small_big_eq]
    assumption
    rw [small_final]
  }
  {
    intro h
    cases h with | intro cs' h
    rcases h with ⟨h, h'⟩ 
    rcases cs with ⟨c, s⟩ 
    rcases cs' with ⟨c', t⟩ 
    exists t
    rw [small_big_eq]
    have hc' : (c' = SKIP) := by
      rw [<- small_final]
      assumption
    rw [<- hc']
    assumption
  }

