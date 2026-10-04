import CaseStudies.WorkloadJobs
-- @@PROOF@@
by
  intro tsk_other R_other t hnci hmem
  obtain ⟨L, hnd, hL, hw⟩ := CaseStudies.WorkloadJobs.workload_as_jobs job_task sched tsk_other
    (t0 sched j) (t0 sched j + t)
  rw [hw]
  -- every job contributing to the workload arrives within the window (no carry-in)
  have hinfo : ∀ x ∈ L, arrives_in arr_seq x ∧ job_task x = tsk_other ∧ t0 sched j ≤ job_arrival x := by
    intro x hx
    obtain ⟨htk, s, hs1, hs2, hsch⟩ := hL x hx
    have harr := H_jobs_come_from_arrival_sequence x s hsch
    refine ⟨harr, htk, ?_⟩
    by_contra hlt
    have hc := hnci x harr htk (by tomega)
    have := CaseStudies.WorkloadJobs.not_completed_of_scheduled_later job_arrival job_cost sched
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute x _ s hs1 hsch
    rw [hc] at this; exact Bool.noConfusion this
  cases L with
  | nil => simp [sumSeq]
  | cons x0 L0 =>
    have hp : 0 < task_period tsk_other := by
      obtain ⟨harr, htk, _⟩ := hinfo x0 List.mem_cons_self
      have := (H_valid_task_parameters _ (htk ▸ H_all_jobs_from_taskset x0 harr)).2.1
      simpa [task_period_positive] using this
    generalize hLdef : x0 :: L0 = L at hnd hL hinfo ⊢
    have hle : sumSeq L (fun x => service_during sched x (t0 sched j) (t0 sched j + t)) ≤
        sumSeq (L.map (fun x => job_arrival x - t0 sched j))
          (fun y => min (task_cost tsk_other) (t - y)) := by
      have : sumSeq (L.map (fun x => job_arrival x - t0 sched j))
          (fun y => min (task_cost tsk_other) (t - y)) =
          sumSeq L (fun x => min (task_cost tsk_other) (t - (job_arrival x - t0 sched j))) := by
        unfold sumSeq; rw [List.map_map]; rfl
      rw [this]
      apply CaseStudies.Common.sumSeq_le_sumSeq
      intro x hx
      obtain ⟨harr, htk, hge⟩ := hinfo x hx
      apply le_min
      · have h1 := CaseStudies.WorkloadJobs.service_during_le_remaining job_cost sched
          H_completed_jobs_dont_execute x (t0 sched j) (t0 sched j + t) (Nat.le_add_right _ _)
        have h2 := (H_valid_job_parameters x harr).2.1
        simp only [job_cost_le_task_cost, decide_eq_true_eq, htk] at h2
        tomega
      · have := CaseStudies.WorkloadJobs.service_during_le_after_arrival job_arrival sched
          H_sequential_jobs H_jobs_must_arrive_to_execute x (t0 sched j) (t0 sched j + t) hge
        tomega
    refine le_trans hle (le_of_le_of_eq (CaseStudies.WorkloadArith.sum_sep_le _ _ hp _ ?_ t) rfl)
    rw [List.pairwise_map]
    apply hnd.imp_of_mem
    intro a b ha hb hab
    obtain ⟨harra, hta, hgea⟩ := hinfo a ha
    obtain ⟨harrb, htb, hgeb⟩ := hinfo b hb
    rcases Nat.le_total (job_arrival a) (job_arrival b) with h | h
    · have := H_sporadic_tasks a b hab harra harrb (hta.trans htb.symm) h
      rw [hta] at this; left; tomega
    · have := H_sporadic_tasks b a (Ne.symm hab) harrb harra (htb.trans hta.symm) h
      rw [htb] at this; right; tomega
