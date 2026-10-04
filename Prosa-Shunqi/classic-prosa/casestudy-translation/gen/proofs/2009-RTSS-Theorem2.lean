/-- LEAN_HELPER: each `R_phi_term` is at most the corresponding `R_term`. -/
theorem R_phi_term_le_R_term {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_period : sporadic_task → time) (tsk : sporadic_task) (chi_min : Nat → time) (phi : time) (h : Nat) :
    R_phi_term task_period tsk chi_min phi h ≤ R_term task_period tsk chi_min h := by
  unfold R_phi_term R_term
  exact Nat.sub_le_sub_left (Nat.le_add_right _ _) _

/-- LEAN_HELPER: the running maxima compare termwise. -/
theorem max_R_phi_term_le_max_R_term {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_period : sporadic_task → time) (tsk : sporadic_task) (chi_min : Nat → time) (phi : time) :
    ∀ h : Nat, max_R_phi_term task_period tsk chi_min phi h ≤ max_R_term task_period tsk chi_min h
  | 0 => by simp [max_R_phi_term, max_R_term]
  | h + 1 => by
      simp only [max_R_phi_term, max_R_term]
      exact max_le_max (max_R_phi_term_le_max_R_term task_period tsk chi_min phi h)
        (R_phi_term_le_R_term task_period tsk chi_min phi (h + 1))

/-- LEAN_HELPER: `max_R_term` is monotone in the number of jobs. -/
theorem max_R_term_mono {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_period : sporadic_task → time) (tsk : sporadic_task) (chi_min : Nat → time) :
    ∀ {a b : Nat}, a ≤ b → max_R_term task_period tsk chi_min a ≤ max_R_term task_period tsk chi_min b := by
  intro a b hab
  induction b with
  | zero => rw [Nat.le_zero.mp hab]
  | succ b ih =>
      rcases Nat.lt_or_ge a (b + 1) with h | h
      · exact le_trans (ih (Nat.lt_succ_iff.mp h)) (by simp only [max_R_term]; exact le_max_left _ _)
      · rw [Nat.le_antisymm hab h]
-- @@PROOF@@
by
  obtain ⟨hH0, hHs, _⟩ := H_is_minimal
  obtain ⟨_, _, hmin⟩ := H_phi_is_minimal
  have hsat : H_phi_satisfy task_period tsk chi_min phi H = true := by
    simp only [H_satisfy, Term, decide_eq_true_eq] at hHs
    simp only [H_phi_satisfy, decide_eq_true_eq]
    exact le_trans hHs (Nat.le_add_right _ _)
  have hle : H_phi ≤ H := hmin H hH0 hsat
  exact CaseStudies.Common.rtb_mono
    (le_trans (max_R_phi_term_le_max_R_term task_period tsk chi_min phi H_phi) (max_R_term_mono task_period tsk chi_min hle))
    Lemma5
