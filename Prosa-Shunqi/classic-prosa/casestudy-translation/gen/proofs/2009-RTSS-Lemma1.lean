-- @@PROOF@@
by
  rw [CaseStudies.Common.sumSeq_toNat_eq_countP]
  rcases t0_left_boundary with h0 | hnb
  · -- no job arrives before time 0
    have : ts.val.countP has_carry_in_b = 0 := by
      rw [List.countP_eq_zero]
      intro k _ hk
      obtain ⟨j0, _, ⟨_, _, hlt, _⟩⟩ := (has_carry_in_P k).mp hk
      tomega
    tomega
  · -- every carry-in task is a higher-priority task scheduled at `t0 - 1`
    have hsub := Prosa.Classic.Util.Counting.sub_in_count _ ts.val has_carry_in_b
      (fun k => task_is_scheduled job_task sched k (t0 sched j - 1) &&
        higher_priority_task higher_eq_priority tsk k) (by
      intro k _ hk
      obtain ⟨j0, htsk, hci⟩ := (has_carry_in_P k).mp hk
      obtain ⟨harr, hhp, hlt, hnc⟩ := hci
      have hs := CaseStudies.Common.carry_in_job_scheduled task_cost task_period task_deadline
        job_arrival job_cost job_task arr_seq ts sched higher_eq_priority H_sporadic_tasks
        H_valid_task_parameters H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence
        H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
        H_priority_transitive H_priority_antisymmetric H_work_conserving H_respects_FP_policy
        H_sequential_tasks tsk task_in_ts (t0 sched j) (Or.inr hnb) j0 harr hhp hlt hnc
      obtain ⟨cpu, hcpu⟩ : ∃ cpu, sched cpu (t0 sched j - 1) = some j0 := by
        simpa [scheduled, scheduled_on, List.any_eq_true] using hs
      have hts : task_is_scheduled job_task sched k (t0 sched j - 1) = true := by
        simp only [task_is_scheduled, List.any_eq_true, List.mem_finRange, true_and]
        exact ⟨cpu, by simp [task_scheduled_on, hcpu, htsk]⟩
      rw [← htsk] at hts ⊢
      simp [hts, hhp])
    have hle := CaseStudies.Common.count_task_is_scheduled_le job_task sched ts (t0 sched j - 1)
      (fun k => task_is_scheduled job_task sched k (t0 sched j - 1) &&
        higher_priority_task higher_eq_priority tsk k) (by
      intro x hx; simp only [Bool.and_eq_true] at hx; exact hx.1)
    have hne : ts.val.countP (fun k => task_is_scheduled job_task sched k (t0 sched j - 1) &&
        higher_priority_task higher_eq_priority tsk k) ≠ num_cpus := hnb
    tomega
