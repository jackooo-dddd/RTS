-- @@PROOF@@
by
  have hv : valid_CI_taskset job_arrival job_cost job_task arr_seq num_cpus sched hp_bounds critical_instant [] :=
    ⟨fun p hp => by simp at hp, List.nodup_nil, by simpa using H_at_least_one_cpu, fun _ _ h => by simp at h⟩
  exact CaseStudies.Common.rtb_mono (H_R_global_upper [] hv) (lemma5 [])
