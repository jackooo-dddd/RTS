import CaseStudies.CommonFp
-- @@PROOF@@
by
  intro R hRd hrec hmin
  unfold response_time_recurrence at hrec
  have hRe : task_cost tsk ≤ R := by tomega
  have hvalid : valid_sporadic_taskset task_cost task_period task_deadline ts.val := by
    intro k hk
    obtain ⟨h1, h2, h3, h4, h5⟩ := H_valid_task_parameters k hk
    simp only [Prosa.Classic.Model.Arrival.Basic.Task.SporadicTask.is_valid_sporadic_task,
      Prosa.Classic.Model.Arrival.Basic.Task.SporadicTask.task_cost_positive,
      Prosa.Classic.Model.Arrival.Basic.Task.SporadicTask.task_period_positive,
      Prosa.Classic.Model.Arrival.Basic.Task.SporadicTask.task_deadline_positive,
      Prosa.Classic.Model.Arrival.Basic.Task.SporadicTask.task_cost_le_deadline,
      Prosa.Classic.Model.Arrival.Basic.Task.SporadicTask.task_cost_le_period, decide_eq_true_eq]
    exact ⟨h1, h2, h3, h4, Nat.le_of_lt h5⟩
  suffices MAIN : ∀ (n : Nat) (j : Job), job_arrival j = n → arrives_in arr_seq j →
      job_task j = tsk → completed job_cost sched j (job_arrival j + R) = true by
    intro j harr htsk
    exact MAIN _ j rfl harr htsk
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro j hn harr htsk
    by_contra hnc
    have hnc' : (!completed job_cost sched j (job_arrival j + R)) = true := by simpa using hnc
    have hprev : ∀ j0 : Job, arrives_in arr_seq j0 → job_task j0 = tsk →
        job_arrival j0 < job_arrival j → completed job_cost sched j0 (job_arrival j0 + R) = true :=
      fun j0 a0 t0 lt => IH _ (hn ▸ lt) j0 rfl a0 t0
    let TI := fun k => task_interference job_arrival job_cost job_task sched j k
      (job_arrival j) (job_arrival j + R)
    have EX := CaseStudies.CommonFp.hp_interference_exceeds task_cost task_period task_deadline
      job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks H_valid_job_parameters ts
      hvalid H_constrained_deadlines H_all_jobs_from_taskset num_cpus sched
      H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute higher_eq_priority H_work_conserving H_respects_FP_policy tsk
      task_in_ts hp_bounds H_response_time_of_interfering_tasks_is_known
      H_hp_bounds_has_interfering_tasks H_interfering_tasks_miss_no_deadlines R hRe hRd j harr htsk
      hnc' hprev
    have hcov := CaseStudies.CommonFp.sum_hp_le_sum_pairs ts
      (fun k => higher_priority_task higher_eq_priority tsk k) (CI_taskset ++ NC_taskset)
      (fun k => min (TI k) (R - task_cost tsk + 1)) (by
        intro k hk hhp
        obtain ⟨R', hR'⟩ := H_hp_bounds_has_interfering_tasks k hk hhp
        have := H_hp_covered_by_CI_or_NC _ hR'
        simp only [Bool.or_eq_true, decide_eq_true_eq] at this
        exact ⟨R', List.mem_append.mpr this⟩)
    rw [CaseStudies.Common.sumSeq_append] at hcov
    have hCI := CaseStudies.Common.sumSeq_le_sumSeq CI_taskset
      (fun p => min (TI p.1) (R - task_cost tsk + 1))
      (fun p => interference_bound_arbitrary_ci task_cost task_period tsk R p) (by
        intro p hp
        obtain ⟨k, Rk⟩ := p
        exact min_le_min_right _ (le_trans
          (task_interference_le_workload job_arrival job_cost job_task sched j k _ _)
          (lemma4 k Rk (job_arrival j) R hp (H_CI_taskset_sub_hp_bounds _ hp))))
    have hNC := CaseStudies.Common.sumSeq_le_sumSeq NC_taskset
      (fun p => min (TI p.1) (R - task_cost tsk + 1))
      (fun p => interference_bound_arbitrary_nc task_cost task_period tsk R p) (by
        intro p hp
        obtain ⟨k, Rk⟩ := p
        exact min_le_min_right _ (le_trans
          (task_interference_le_workload job_arrival job_cost job_task sched j k _ _)
          (lemma2 k Rk (job_arrival j) R hp (H_NC_taskset_sub_hp_bounds _ hp))))
    have hbound : total_interference_bound_rtcsa14 task_cost task_period tsk CI_taskset NC_taskset R =
        sumSeq CI_taskset (fun p => interference_bound_arbitrary_ci task_cost task_period tsk R p) +
          sumSeq NC_taskset (fun p => interference_bound_arbitrary_nc task_cost task_period tsk R p) :=
      rfl
    have htot : (R - task_cost tsk + 1) * num_cpus ≤
        total_interference_bound_rtcsa14 task_cost task_period tsk CI_taskset NC_taskset R := by
      rw [hbound]; exact le_trans EX (le_trans hcov (Nat.add_le_add hCI hNC))
    have hdiv := (Nat.le_div_iff_mul_le H_at_least_one_cpu).mpr htot
    unfold div_floor at hrec
    tomega
