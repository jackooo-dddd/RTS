import CaseStudies.BusyWindow
import CaseStudies.CommonFp
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
  intro t ht he
  have hfin := f_is_finish_time
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hfin
  have hnc : completed job_cost sched j (t0 sched j + t) = false := by
    cases hc : completed job_cost sched j (t0 sched j + t)
    · rfl
    · have := completion_monotonic job_cost sched j _ (f - 1) (by tomega) hc
      rw [this] at hfin; exact absurd hfin.1 (by simp)
  have hcost : job_cost j ≤ task_cost tsk := by
    have := (H_valid_job_parameters j H_j_arrives).2.1
    simp only [job_cost_le_task_cost, decide_eq_true_eq] at this
    rw [H_job_of_tsk] at this; exact this
  have hprev : ∀ j0 : Job, arrives_in arr_seq j0 → job_task j0 = tsk →
      job_arrival j0 < job_arrival j → completed job_cost sched j0 (job_arrival j) = true := by
    intro j0 a0 h0 lt
    have hne : j0 ≠ j := by rintro rfl; exact absurd lt (Nat.lt_irrefl _)
    have SPO := H_sporadic_tasks j0 j hne a0 H_j_arrives (h0.trans H_job_of_tsk.symm) (le_of_lt lt)
    rw [h0] at SPO
    have hdp := H_constrained_deadlines tsk task_in_ts
    exact completion_monotonic job_cost sched j0 _ _ (by tomega)
      (H_previous_jobs_of_tsk_completed j0 a0 h0 lt)
  have EX := CaseStudies.BusyWindow.busy_window_sum_min_ge task_cost task_period task_deadline
    job_arrival job_cost job_task arr_seq ts sched higher_eq_priority H_sporadic_tasks
    H_valid_task_parameters H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence
    H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving
    H_respects_FP_policy H_sequential_tasks tsk j H_j_arrives H_job_of_tsk hcost (t0 sched j)
    t0_leq_arrival_time (fun s h1 h2 => cpu_busy_during_t0_rk s (by simp [h1, h2])) hprev t he hnc
  let G := fun p : sporadic_task × time =>
    min (workload job_task sched p.1 (t0 sched j) (t0 sched j + t)) (t - task_cost tsk + 1)
  have hcov := CaseStudies.CommonFp.sum_hp_le_sum_pairs ts
    (fun k => higher_priority_task higher_eq_priority tsk k) hp_bounds
    (fun k => min (workload job_task sched k (t0 sched j) (t0 sched j + t)) (t - task_cost tsk + 1))
    H_hp_bounds_has_interfering_tasks
  rw [CaseStudies.Common.sumSeq_perm _ (perm_CI_NC task_cost task_period tsk hp_bounds t num_cpus
    Huniq_hp_bounds), CaseStudies.Common.sumSeq_append] at hcov
  have hCI := CaseStudies.Common.sumSeq_le_sumSeq
    (CI_taskset task_cost task_period tsk hp_bounds t num_cpus) G
    (fun p => interference_bound_generic task_cost task_period tsk t p) (by
      intro p hp
      obtain ⟨k, Rk⟩ := p
      exact min_le_min_right _ (H_Lemma2_2 k Rk (t0 sched j) t hp))
  have hNC := CaseStudies.Common.sumSeq_le_sumSeq
    (NC_taskset task_cost task_period tsk hp_bounds t num_cpus) G
    (fun p => interference_bound_nc task_cost task_period tsk t p) (by
      intro p hp
      obtain ⟨k, Rk⟩ := p
      exact min_le_min_right _ (H_Lemma2_1 k Rk (t0 sched j) t hp))
  have hgn : total_interference_bound_gn task_cost task_period tsk hp_bounds t num_cpus =
      sumSeq (NC_taskset task_cost task_period tsk hp_bounds t num_cpus)
          (fun p => interference_bound_nc task_cost task_period tsk t p) +
        sumSeq (CI_taskset task_cost task_period tsk hp_bounds t num_cpus)
          (fun p => interference_bound_generic task_cost task_period tsk t p) := rfl
  have htot : (t - task_cost tsk + 1) * num_cpus ≤
      total_interference_bound_gn task_cost task_period tsk hp_bounds t num_cpus := by
    rw [hgn, Nat.mul_comm]
    exact le_trans EX (le_trans hcov ((Nat.add_le_add hCI hNC).trans (le_of_eq (Nat.add_comm _ _))))
  have hdiv := (Nat.le_div_iff_mul_le H_at_least_one_cpu).mpr htot
  unfold div_floor
  tomega
