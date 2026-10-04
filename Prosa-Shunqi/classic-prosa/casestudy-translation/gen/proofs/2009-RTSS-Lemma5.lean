import CaseStudies.BusyWindow
import CaseStudies.CommonFp
/-- LEAN_HELPER: the higher-priority bounds are a permutation of the carry-in set followed by the no-carry-in set. -/
theorem perm_CI_NC {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task) (R_prev : List (sporadic_task × time))
    (delta : time) (num_cpus h : Nat) (hnd : R_prev.Nodup) :
    R_prev.Perm (CI_taskset task_cost task_period tsk R_prev delta num_cpus h ++
      NC_taskset task_cost task_period tsk R_prev delta num_cpus h) := by
  unfold NC_taskset CI_taskset
  convert CaseStudies.Common.perm_take_append_filter (List.mergeSort_perm _ _) hnd (num_cpus - 1)

/-- LEAN_HELPER: `max_R_phi_term` dominates its first term. -/
theorem R_phi_term_one_le_max {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_period : sporadic_task → time) (tsk : sporadic_task) (chi_min : Nat → time) (phi : time) :
    ∀ n : Nat, 1 ≤ n → R_phi_term task_period tsk chi_min phi 1 ≤ max_R_phi_term task_period tsk chi_min phi n
  | 0, h => absurd h (by decide)
  | 1, _ => by simp [max_R_phi_term]
  | n + 2, _ => le_trans (R_phi_term_one_le_max task_period tsk chi_min phi (n + 1) (by omega))
      (le_max_left _ _)
-- @@PROOF@@
by
  have hp_tsk : 0 < task_period tsk := by
    have := (H_valid_task_parameters tsk task_in_ts).2.1
    simpa [Prosa.Classic.Model.Arrival.Basic.Task.SporadicTask.task_period_positive] using this
  -- (1) the job `j` alone is a tight chain
  have hfirst : (first_h_jobs_through job_arrival job_task arr_seq tsk j j).length = 1 ∧
      j ∈ first_h_jobs_through job_arrival job_task arr_seq tsk j j := by
    have heq : first_h_jobs_through job_arrival job_task arr_seq tsk j j =
        (jobs_arriving_at arr_seq (job_arrival j)).filter (is_job_of_task job_task tsk) := by
      simp [first_h_jobs_through, jobs_of_tsk_between, arrivals_of_task_between,
        jobs_arrived_between, Prosa.Util.Notation.bigCat]
    rw [heq]
    have hjmem : j ∈ (jobs_arriving_at arr_seq (job_arrival j)).filter (is_job_of_task job_task tsk) := by
      obtain ⟨t, ht⟩ := H_j_arrives
      have := H_arrival_times_are_consistent j t (by simp [arrives_at, ht])
      rw [this]
      exact List.mem_filter.mpr ⟨ht, by simp [is_job_of_task, H_job_of_tsk]⟩
    refine ⟨?_, hjmem⟩
    have hsub : ∀ x ∈ (jobs_arriving_at arr_seq (job_arrival j)).filter (is_job_of_task job_task tsk),
        x ∈ [j] := by
      intro x hx
      rw [List.mem_filter] at hx
      obtain ⟨hxa, hxt⟩ := hx
      simp only [is_job_of_task, decide_eq_true_eq] at hxt
      have harx : arrives_in arr_seq x := ⟨_, hxa⟩
      have hax := H_arrival_times_are_consistent x (job_arrival j) (by simpa [arrives_at] using hxa)
      rw [List.mem_singleton]
      by_contra hne
      have := H_sporadic_tasks x j hne harx H_j_arrives (hxt.trans H_job_of_tsk.symm) (le_of_eq hax)
      rw [hxt] at this
      tomega
    have hle := (List.subperm_of_subset ((H_arrival_sequence_is_a_set _).filter _) hsub).length_le
    have hpos := List.length_pos_of_mem hjmem
    simp only [List.length_singleton] at hle
    omega
  have hhth : job_is_hth_after_j task_period job_arrival job_task arr_seq tsk j 1 j :=
    ⟨le_refl _, H_j_arrives, H_job_of_tsk, by simp, hfirst.1, hfirst.2⟩
  have hchain : tight_chain_ending_at task_period job_arrival job_cost job_task arr_seq num_cpus sched
      tsk j 1 j := by
    refine ⟨hhth, H_previous_jobs_of_tsk_completed, ?_, ?_, ?_⟩
    · intro h h1 h2
      have : h = 1 := by omega
      subst this
      exact ⟨j, hhth⟩
    · intro h _ _ h1 h2; omega
    · intro h _ _ h1 h2; omega
  obtain ⟨hw, jw, fw, hle, hwth, hfin, hlt, hworst⟩ :=
    H_Lemma1_selects_worstcase_job_from_tight_chain 1 j hchain
  obtain ⟨hw1, hwarr, hwtsk, hwa, _, _⟩ := hwth
  have hw_eq : hw = 1 := by omega
  subst hw_eq
  have haw : job_arrival jw = job_arrival j := by simpa using hwa
  -- (2) the selected job finishes within `chi_min 1` of `t0`
  obtain ⟨hchi_sol, _⟩ := chi_min_spec 1
  unfold f_chi at hchi_sol
  have hfinw := hfin
  simp only [job_finishes_at, Bool.and_eq_true, Bool.not_eq_true'] at hfinw
  have hchi_e : task_cost tsk ≤ chi_min 1 := by tomega
  have hbound : fw ≤ t0 sched j + chi_min 1 := by
    by_contra hgt
    have hnc : completed job_cost sched jw (t0 sched j + chi_min 1) = false := by
      cases hc : completed job_cost sched jw (t0 sched j + chi_min 1)
      · rfl
      · have := completion_monotonic job_cost sched jw _ (fw - 1) (by tomega) hc
        rw [this] at hfinw; exact absurd hfinw.1 (by simp)
    have hcost : job_cost jw ≤ task_cost tsk := by
      have := (H_valid_job_parameters jw hwarr).2.1
      simp only [job_cost_le_task_cost, decide_eq_true_eq] at this
      rw [hwtsk] at this; exact this
    have EX := CaseStudies.BusyWindow.busy_window_sum_min_ge task_cost task_period task_deadline
      job_arrival job_cost job_task arr_seq ts sched higher_eq_priority H_sporadic_tasks
      H_valid_task_parameters H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence
      H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
      H_work_conserving H_respects_FP_policy H_sequential_tasks tsk jw hwarr hwtsk hcost
      (t0 sched j) (by rw [haw]; exact t0_leq_arrival_time)
      (fun s h1 h2 => cpu_busy_during_t0_rk s (by rw [haw] at h2; simp [h1, h2]))
      (fun j0 a0 h0 lt => by
        rw [haw] at lt ⊢; exact H_previous_jobs_of_tsk_completed j0 a0 h0 lt)
      (chi_min 1) hchi_e hnc
    let G := fun p : sporadic_task × time =>
      min (workload job_task sched p.1 (t0 sched j) (t0 sched j + chi_min 1))
        (chi_min 1 - task_cost tsk + 1)
    have hcov := CaseStudies.CommonFp.sum_hp_le_sum_pairs ts
      (fun k => higher_priority_task higher_eq_priority tsk k) hp_bounds
      (fun k => min (workload job_task sched k (t0 sched j) (t0 sched j + chi_min 1))
        (chi_min 1 - task_cost tsk + 1))
      H_hp_bounds_has_interfering_tasks
    rw [CaseStudies.Common.sumSeq_perm _ (perm_CI_NC task_cost task_period tsk hp_bounds (chi_min 1)
      num_cpus 1 Huniq_hp_bounds), CaseStudies.Common.sumSeq_append] at hcov
    have hCI := CaseStudies.Common.sumSeq_le_sumSeq
      (CI_taskset task_cost task_period tsk hp_bounds (chi_min 1) num_cpus 1) G
      (fun p => interference_bound_arbitrary_ci task_cost task_period tsk (chi_min 1) p 1) (by
        intro p hp
        obtain ⟨k, Rk⟩ := p
        show _ ≤ min _ (chi_min 1 - 1 * task_cost tsk + 1)
        rw [Nat.one_mul]
        exact min_le_min_right _ (H_Lemma2_2 k Rk (t0 sched j) 1 (chi_min 1) hp))
    have hNC := CaseStudies.Common.sumSeq_le_sumSeq
      (NC_taskset task_cost task_period tsk hp_bounds (chi_min 1) num_cpus 1) G
      (fun p => interference_bound_arbitrary_nc task_cost task_period tsk (chi_min 1) p 1) (by
        intro p hp
        obtain ⟨k, Rk⟩ := p
        show _ ≤ min _ (chi_min 1 - 1 * task_cost tsk + 1)
        rw [Nat.one_mul]
        exact min_le_min_right _ (H_Lemma2_1 k Rk (t0 sched j) 1 (chi_min 1) hp))
    have hgn : total_interference_bound_gn_arbitrary task_cost task_period tsk hp_bounds (chi_min 1)
        num_cpus 1 =
        sumSeq (NC_taskset task_cost task_period tsk hp_bounds (chi_min 1) num_cpus 1)
            (fun p => interference_bound_arbitrary_nc task_cost task_period tsk (chi_min 1) p 1) +
          sumSeq (CI_taskset task_cost task_period tsk hp_bounds (chi_min 1) num_cpus 1)
            (fun p => interference_bound_arbitrary_ci task_cost task_period tsk (chi_min 1) p 1) := rfl
    have htot : (chi_min 1 - task_cost tsk + 1) * num_cpus ≤
        total_interference_bound_gn_arbitrary task_cost task_period tsk hp_bounds (chi_min 1)
          num_cpus 1 := by
      rw [hgn, Nat.mul_comm]
      exact le_trans EX (le_trans hcov ((Nat.add_le_add hCI hNC).trans (le_of_eq (Nat.add_comm _ _))))
    have hdiv := (Nat.le_div_iff_mul_le H_at_least_one_cpu).mpr htot
    unfold div_floor at hchi_sol
    tomega
  -- (3) every job of `tsk` completes within the bound
  intro j0 harr0 htsk0
  apply hworst j0 _ harr0 htsk0
  apply completion_monotonic job_cost sched jw fw _ _ hfinw.2
  have h1 := R_phi_term_one_le_max task_period tsk chi_min phi H_phi H_phi_is_minimal.1
  unfold R_phi_term at h1
  simp only [Nat.sub_self, Nat.zero_mul, Nat.zero_add] at h1
  rw [phi_is_defined] at h1 ⊢
  rw [haw] at hlt ⊢
  have e1 := hbound
  have e2 := t0_leq_arrival_time
  generalize max_R_phi_term task_period tsk chi_min (job_arrival j - t0 sched j) H_phi = M at h1 ⊢
  generalize chi_min 1 = C at h1 e1
  generalize t0 sched j = T at h1 e1 e2
  tomega
