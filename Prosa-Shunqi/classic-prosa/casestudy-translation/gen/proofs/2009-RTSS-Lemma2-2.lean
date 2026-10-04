import CaseStudies.WorkloadJobs
-- @@PROOF@@
by
  intro tsk_other R_other t hci hmem
  obtain ⟨j0, htask0, hci0⟩ := hci
  have hci0' := hci0
  obtain ⟨harr0, hhp0, hlt0, hnc0⟩ := hci0'
  have hin : tsk_other ∈ ts := htask0 ▸ H_all_jobs_from_taskset j0 harr0
  have hvalid := H_valid_task_parameters tsk_other hin
  have hp : 0 < task_period tsk_other := by simpa [task_period_positive] using hvalid.2.1
  have he : 1 ≤ task_cost tsk_other := by
    have := hvalid.1; simp only [task_cost_positive, decide_eq_true_eq] at this; exact this
  have heR := H_response_time_ge_cost tsk_other R_other hmem
  have hRp : R_other ≤ task_period tsk_other :=
    le_trans (H_no_deadline_miss tsk_other R_other hmem) (H_constrained_deadlines tsk_other hin)
  have hcomp0 := H_response_time_of_interfering_tasks_is_known tsk_other R_other hmem j0 harr0 htask0
  -- `j0` arrived `δ ∈ [1, R)` before the window
  have hδR : t0 sched j < job_arrival j0 + R_other := by
    by_contra h
    have := completion_monotonic job_cost sched j0 _ (t0 sched j) (by tomega) hcomp0
    simp [this] at hnc0
  obtain ⟨L, hnd, hL, hw⟩ := CaseStudies.WorkloadJobs.workload_as_jobs job_task sched tsk_other
    (t0 sched j) (t0 sched j + t)
  rw [hw]
  -- the other contributing jobs arrive in the window, at least `p` after `j0`
  have hinfo : ∀ x ∈ L, x ≠ j0 → arrives_in arr_seq x ∧ job_task x = tsk_other ∧
      t0 sched j ≤ job_arrival x ∧ job_arrival j0 + task_period tsk_other ≤ job_arrival x := by
    intro x hx hne
    obtain ⟨htk, s, hs1, hs2, hsch⟩ := hL x hx
    have harr := H_jobs_come_from_arrival_sequence x s hsch
    have hge : t0 sched j ≤ job_arrival x := by
      by_contra hlt
      have hncx := CaseStudies.WorkloadJobs.not_completed_of_scheduled_later job_arrival job_cost
        sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute x _ s hs1 hsch
      have hcix : is_carry_in_job job_arrival job_cost job_task arr_seq num_cpus sched tsk
          higher_eq_priority j t0 x :=
        ⟨harr, by rw [htk, ← htask0]; exact hhp0, by tomega, by simp [hncx]⟩
      exact hne (carry_in_job_unique tsk_other x j0 htk hcix htask0 hci0)
    refine ⟨harr, htk, hge, ?_⟩
    have := H_sporadic_tasks j0 x (Ne.symm hne) harr0 harr (htask0.trans htk.symm) (by tomega)
    rwa [htask0] at this
  -- split off `j0`
  have hsplit : sumSeq L (fun x => service_during sched x (t0 sched j) (t0 sched j + t)) ≤
      service_during sched j0 (t0 sched j) (t0 sched j + t) +
        sumSeq (L.erase j0) (fun x => service_during sched x (t0 sched j) (t0 sched j + t)) := by
    by_cases hj0 : j0 ∈ L
    · rw [CaseStudies.Common.sumSeq_perm _ (List.perm_cons_erase hj0)]
      unfold sumSeq; simp
    · rw [List.erase_of_not_mem hj0]; exact Nat.le_add_left _ _
  have herase : ∀ x ∈ L.erase j0, x ∈ L ∧ x ≠ j0 := by
    intro x hx
    exact ⟨List.mem_of_mem_erase hx, fun h => by subst h; exact (hnd.mem_erase_iff.mp hx).1 rfl⟩
  -- the carry-in job
  have hci_bound : service_during sched j0 (t0 sched j) (t0 sched j + t) ≤
      min (task_cost tsk_other - 1) (R_other - (t0 sched j - job_arrival j0)) := by
    apply le_min
    · have h1 := CaseStudies.WorkloadJobs.service_during_le_remaining job_cost sched
        H_completed_jobs_dont_execute j0 (t0 sched j) (t0 sched j + t) (Nat.le_add_right _ _)
      have h2 := Lemma1_09 tsk_other j0 htask0 hci0
      unfold carry_in_workload at h2
      tomega
    · have := CaseStudies.WorkloadJobs.service_during_le_before_completion job_cost sched
        H_sequential_jobs H_completed_jobs_dont_execute j0 (t0 sched j) (t0 sched j + t) _ hcomp0
      tomega
  -- the later jobs
  have hbody : sumSeq (L.erase j0) (fun x => service_during sched x (t0 sched j) (t0 sched j + t)) ≤
      CaseStudies.WorkloadArith.wnc (task_cost tsk_other) (task_period tsk_other)
        (t - (task_period tsk_other - (t0 sched j - job_arrival j0))) := by
    have hle : sumSeq (L.erase j0) (fun x => service_during sched x (t0 sched j) (t0 sched j + t)) ≤
        sumSeq ((L.erase j0).map (fun x => job_arrival x - t0 sched j))
          (fun y => min (task_cost tsk_other) (t - y)) := by
      have : sumSeq ((L.erase j0).map (fun x => job_arrival x - t0 sched j))
          (fun y => min (task_cost tsk_other) (t - y)) =
          sumSeq (L.erase j0) (fun x => min (task_cost tsk_other) (t - (job_arrival x - t0 sched j))) := by
        unfold sumSeq; rw [List.map_map]; rfl
      rw [this]
      apply CaseStudies.Common.sumSeq_le_sumSeq
      intro x hx
      obtain ⟨hxL, hne⟩ := herase x hx
      obtain ⟨harr, htk, hge, _⟩ := hinfo x hxL hne
      apply le_min
      · have h1 := CaseStudies.WorkloadJobs.service_during_le_remaining job_cost sched
          H_completed_jobs_dont_execute x (t0 sched j) (t0 sched j + t) (Nat.le_add_right _ _)
        have h2 := (H_valid_job_parameters x harr).2.1
        simp only [job_cost_le_task_cost, decide_eq_true_eq, htk] at h2
        tomega
      · have := CaseStudies.WorkloadJobs.service_during_le_after_arrival job_arrival sched
          H_sequential_jobs H_jobs_must_arrive_to_execute x (t0 sched j) (t0 sched j + t) hge
        tomega
    refine le_trans hle (CaseStudies.WorkloadArith.sum_sep_shift_le _ _ _ hp _ ?_ ?_ t)
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
      obtain ⟨hxL, hne⟩ := herase x hx
      obtain ⟨_, _, hge, hsep⟩ := hinfo x hxL hne
      tomega
    · rw [List.pairwise_map]
      apply (hnd.sublist (List.erase_sublist)).imp_of_mem
      intro a b ha hb hab
      obtain ⟨haL, hane⟩ := herase a ha
      obtain ⟨hbL, hbne⟩ := herase b hb
      obtain ⟨harra, hta, hgea, _⟩ := hinfo a haL hane
      obtain ⟨harrb, htb, hgeb, _⟩ := hinfo b hbL hbne
      rcases Nat.le_total (job_arrival a) (job_arrival b) with h | h
      · have := H_sporadic_tasks a b hab harra harrb (hta.trans htb.symm) h
        rw [hta] at this; left; tomega
      · have := H_sporadic_tasks b a (Ne.symm hab) harrb harra (htb.trans hta.symm) h
        rw [htb] at this; right; tomega
  have harith := CaseStudies.WorkloadArith.ci09_arith (task_cost tsk_other) (task_period tsk_other)
    R_other (t0 sched j - job_arrival j0) he heR hRp (by tomega) (by tomega) t
  refine le_trans hsplit (le_trans (Nat.add_le_add hci_bound hbody) (le_of_le_of_eq harith ?_))
  rfl
