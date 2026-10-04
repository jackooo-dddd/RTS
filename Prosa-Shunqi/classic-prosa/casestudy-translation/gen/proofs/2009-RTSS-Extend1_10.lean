/-- LEAN_HELPER: the higher-priority bounds are a permutation of the carry-in set followed by the no-carry-in set. -/
theorem perm_CI_NC {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task) (R_prev : List (sporadic_task × time))
    (delta : time) (num_cpus : Nat) (hnd : R_prev.Nodup) :
    R_prev.Perm (CI_taskset task_cost task_period tsk R_prev delta num_cpus ++
      NC_taskset task_cost task_period tsk R_prev delta num_cpus) := by
  unfold NC_taskset CI_taskset
  convert CaseStudies.Common.perm_take_append_filter (List.mergeSort_perm _ _) hnd (num_cpus - 1)
-- @@PROOF@@
by
  by_contra hneg
  simp only [not_or, not_exists, not_and, not_lt] at hneg
  obtain ⟨hCI, hNC⟩ := hneg
  let F : sporadic_task × time → Nat := fun p =>
    min (task_interference job_arrival job_cost job_task sched j p.1 (job_arrival j) (job_arrival j + R))
      (R - task_cost tsk + 1)
  have hperm := perm_CI_NC task_cost task_period tsk hp_bounds R num_cpus Huniq_hp_bounds
  have hsum : sumSeq hp_bounds F =
      sumSeq (CI_taskset task_cost task_period tsk hp_bounds R num_cpus) F +
        sumSeq (NC_taskset task_cost task_period tsk hp_bounds R num_cpus) F := by
    rw [CaseStudies.Common.sumSeq_perm F hperm, CaseStudies.Common.sumSeq_append]
  have hci := CaseStudies.Common.sumSeq_le_sumSeq (CI_taskset task_cost task_period tsk hp_bounds R num_cpus) F
    (fun p => interference_bound_generic task_cost task_period tsk R p)
    (fun p hp => by obtain ⟨a, b⟩ := p; exact hCI a b hp)
  have hnc := CaseStudies.Common.sumSeq_le_sumSeq (NC_taskset task_cost task_period tsk hp_bounds R num_cpus) F
    (fun p => interference_bound_nc task_cost task_period tsk R p)
    (fun p hp => by obtain ⟨a, b⟩ := p; exact hNC a b hp)
  have hgn : total_interference_bound_gn task_cost task_period tsk hp_bounds R num_cpus =
      sumSeq (NC_taskset task_cost task_period tsk hp_bounds R num_cpus)
          (fun p => interference_bound_nc task_cost task_period tsk R p) +
        sumSeq (CI_taskset task_cost task_period tsk hp_bounds R num_cpus)
          (fun p => interference_bound_generic task_cost task_period tsk R p) := rfl
  have h9 : total_interference_bound_gn task_cost task_period tsk hp_bounds R num_cpus < sumSeq hp_bounds F :=
    Method1_9
  omega
