-- @@PROOF@@
by
  have hfin : completed job_cost sched j f = true := by
    simp only [Bool.and_eq_true] at f_is_finish_time; exact f_is_finish_time.2
  have hchi_e : task_cost tsk ≤ chi := by
    have := chi_is_solution; tomega
  have hf : f - t0 sched j ≤ chi := by
    by_contra hlt
    have h3 := Lemma3 chi (by tomega) hchi_e
    have := chi_is_solution
    tomega
  intro j0 harr htsk
  apply j_has_worstcase_responsetime j0 _ harr htsk
  exact completion_monotonic job_cost sched j f _ (by tomega) hfin
