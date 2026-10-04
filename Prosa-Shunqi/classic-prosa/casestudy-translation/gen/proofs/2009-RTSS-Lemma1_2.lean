-- @@PROOF@@
by
  intro tsk_other j0 htsk hci
  obtain ⟨harr, hhp, hlt, hnc⟩ := hci
  -- the carry-in job is pending at `t0 - 1`, which is not hp-busy, so it is scheduled there
  have hs := CaseStudies.Common.carry_in_job_scheduled task_cost task_period task_deadline
    job_arrival job_cost job_task arr_seq ts sched higher_eq_priority H_sporadic_tasks
    H_valid_task_parameters H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence
    H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    H_priority_transitive H_priority_antisymmetric H_work_conserving H_respects_FP_policy
    H_sequential_tasks tsk task_in_ts (t0 sched j) t0_left_boundary j0 harr hhp hlt hnc
  have h1 := CaseStudies.Common.service_pos_of_scheduled sched j0 _ hs
  have hcost : job_cost j0 ≤ task_cost tsk_other := by
    have := (H_valid_job_parameters j0 harr).2.1
    simp only [job_cost_le_task_cost, decide_eq_true_eq] at this
    rw [← htsk]; exact this
  have ht : t0 sched j - 1 + 1 = t0 sched j := by tomega
  rw [ht] at h1
  unfold carry_in_workload
  tomega
