/-- LEAN_HELPER: a per-task bound of the form `min _ (delta - e + 1)` is at most one at `delta = e`. -/
theorem ib_generic_at_cost_le_one {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task) (p : sporadic_task × time) :
    interference_bound_generic task_cost task_period tsk (task_cost tsk) p ≤ 1 := by
  unfold interference_bound_generic
  exact le_trans (min_le_right _ _) (by simp)

theorem ib_nc_at_cost_le_one {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task) (p : sporadic_task × time) :
    interference_bound_nc task_cost task_period tsk (task_cost tsk) p ≤ 1 := by
  unfold interference_bound_nc
  exact le_trans (min_le_right _ _) (by simp)

/-- LEAN_HELPER: with fewer than `m` pairs, the carry-in set is all of them and the no-carry-in set is empty. -/
theorem NC_taskset_nil_of_short {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task) (R_prev : List (sporadic_task × time))
    (delta : time) (num_cpus : Nat) (h : R_prev.length < num_cpus) :
    NC_taskset task_cost task_period tsk R_prev delta num_cpus = [] := by
  unfold NC_taskset CI_taskset
  rw [List.take_of_length_le (by rw [List.length_mergeSort]; omega)]
  rw [List.filter_eq_nil_iff]
  intro p hp
  simp [List.mem_mergeSort, hp]

theorem CI_taskset_length_of_short {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task) (R_prev : List (sporadic_task × time))
    (delta : time) (num_cpus : Nat) (h : R_prev.length < num_cpus) :
    (CI_taskset task_cost task_period tsk R_prev delta num_cpus).length = R_prev.length := by
  unfold CI_taskset
  rw [List.take_of_length_le (by rw [List.length_mergeSort]; omega), List.length_mergeSort]
-- @@PROOF@@
by
  intro hn
  rw [CaseStudies.Common.sumSeq_one] at hn
  -- the cost solves both recurrences
  have hgn : total_interference_bound_gn task_cost task_period tsk hp_bounds (task_cost tsk) num_cpus < num_cpus := by
    unfold total_interference_bound_gn
    rw [NC_taskset_nil_of_short task_cost task_period tsk hp_bounds _ num_cpus hn]
    have := CaseStudies.Common.sumSeq_le_length_of_le_one
      (CI_taskset task_cost task_period tsk hp_bounds (task_cost tsk) num_cpus)
      (fun p => interference_bound_generic task_cost task_period tsk (task_cost tsk) p)
      (fun p _ => ib_generic_at_cost_le_one task_cost task_period tsk p)
    rw [CI_taskset_length_of_short task_cost task_period tsk hp_bounds _ num_cpus hn] at this
    simp only [Prosa.Util.Sum.sumSeq, List.map_nil, List.sum_nil, Nat.zero_add]
    exact lt_of_le_of_lt this hn
  have hfp : total_interference_bound_fp task_cost task_period tsk hp_bounds (task_cost tsk) < num_cpus := by
    unfold total_interference_bound_fp
    have := CaseStudies.Common.sumSeq_le_length_of_le_one hp_bounds
      (fun (tsk_other, R_other) =>
        interference_bound_generic task_cost task_period tsk (task_cost tsk) (tsk_other, R_other))
      (fun p _ => ib_generic_at_cost_le_one task_cost task_period tsk p)
    exact lt_of_le_of_lt this hn
  have e1 : task_cost tsk = task_cost tsk + div_floor
      (total_interference_bound_gn task_cost task_period tsk hp_bounds (task_cost tsk) num_cpus) num_cpus := by
    simp [div_floor, Nat.div_eq_of_lt hgn]
  have e2 : task_cost tsk = task_cost tsk + div_floor
      (total_interference_bound_fp task_cost task_period tsk hp_bounds (task_cost tsk)) num_cpus := by
    simp [div_floor, Nat.div_eq_of_lt hfp]
  have l1 := R1_is_least_solution _ e1
  have l2 := R2_is_least_solution _ e2
  constructor
  · have : task_cost tsk ≤ R1 := by rw [H_response_time_recurrence_holds_gn]; exact Nat.le_add_right _ _
    exact Nat.le_antisymm l1 this
  · have : task_cost tsk ≤ R2 := by rw [H_response_time_recurrence_holds_bertogna]; exact Nat.le_add_right _ _
    exact Nat.le_antisymm l2 this
