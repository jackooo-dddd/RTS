From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence CurvesCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations MaximalArrivalSequenceCorrespondence
  FactsMaximalArrivalSequenceCorrespondence.

Goal Logic.True. idtac "AUDIT_BEGIN arr_seq_is_a_set_correspondence". exact Logic.I. Qed.
Print Assumptions arr_seq_is_a_set_correspondence.
Goal Logic.True. idtac "AUDIT_END arr_seq_is_a_set_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN concrete_all_jobs_from_taskset_correspondence". exact Logic.I. Qed.
Print Assumptions concrete_all_jobs_from_taskset_correspondence.
Goal Logic.True. idtac "AUDIT_END concrete_all_jobs_from_taskset_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arrival_times_are_consistent_correspondence". exact Logic.I. Qed.
Print Assumptions arrival_times_are_consistent_correspondence.
Goal Logic.True. idtac "AUDIT_END arrival_times_are_consistent_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN concrete_valid_job_cost_correspondence". exact Logic.I. Qed.
Print Assumptions concrete_valid_job_cost_correspondence.
Goal Logic.True. idtac "AUDIT_END concrete_valid_job_cost_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN task_arrivals_at_eq_generate_jobs_at_correspondence". exact Logic.I. Qed.
Print Assumptions task_arrivals_at_eq_generate_jobs_at_correspondence.
Goal Logic.True. idtac "AUDIT_END task_arrivals_at_eq_generate_jobs_at_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN task_arrivals_at_eq_correspondence". exact Logic.I. Qed.
Print Assumptions task_arrivals_at_eq_correspondence.
Goal Logic.True. idtac "AUDIT_END task_arrivals_at_eq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN number_of_task_arrivals_eq_correspondence". exact Logic.I. Qed.
Print Assumptions number_of_task_arrivals_eq_correspondence.
Goal Logic.True. idtac "AUDIT_END number_of_task_arrivals_eq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN extend_horizon_size_correspondence". exact Logic.I. Qed.
Print Assumptions extend_horizon_size_correspondence.
Goal Logic.True. idtac "AUDIT_END extend_horizon_size_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN prefix_up_to_size_correspondence". exact Logic.I. Qed.
Print Assumptions prefix_up_to_size_correspondence.
Goal Logic.True. idtac "AUDIT_END prefix_up_to_size_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN n_arrivals_at_prefix_inclusion1_correspondence". exact Logic.I. Qed.
Print Assumptions n_arrivals_at_prefix_inclusion1_correspondence.
Goal Logic.True. idtac "AUDIT_END n_arrivals_at_prefix_inclusion1_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN n_arrivals_at_prefix_inclusion_correspondence". exact Logic.I. Qed.
Print Assumptions n_arrivals_at_prefix_inclusion_correspondence.
Goal Logic.True. idtac "AUDIT_END n_arrivals_at_prefix_inclusion_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN max_arrivals_at_next_max_arrivals_eq_correspondence". exact Logic.I. Qed.
Print Assumptions max_arrivals_at_next_max_arrivals_eq_correspondence.
Goal Logic.True. idtac "AUDIT_END max_arrivals_at_next_max_arrivals_eq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN n_arrivals_at_leq_correspondence". exact Logic.I. Qed.
Print Assumptions n_arrivals_at_leq_correspondence.
Goal Logic.True. idtac "AUDIT_END n_arrivals_at_leq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN concrete_is_arrival_curve_correspondence". exact Logic.I. Qed.
Print Assumptions concrete_is_arrival_curve_correspondence.
Goal Logic.True. idtac "AUDIT_END concrete_is_arrival_curve_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fma_forall_cover_sprop". exact Logic.I. Qed.
Print Assumptions fma_forall_cover_sprop.
Goal Logic.True. idtac "AUDIT_END fma_forall_cover_sprop". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fma_eq_correspondence". exact Logic.I. Qed.
Print Assumptions fma_eq_correspondence.
Goal Logic.True. idtac "AUDIT_END fma_eq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fma_list_bridge". exact Logic.I. Qed.
Print Assumptions fma_list_bridge.
Goal Logic.True. idtac "AUDIT_END fma_list_bridge". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fma_svc_to_ar". exact Logic.I. Qed.
Print Assumptions fma_svc_to_ar.
Goal Logic.True. idtac "AUDIT_END fma_svc_to_ar". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fma_ar_to_svc". exact Logic.I. Qed.
Print Assumptions fma_ar_to_svc.
Goal Logic.True. idtac "AUDIT_END fma_ar_to_svc". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fma_list_source_total". exact Logic.I. Qed.
Print Assumptions fma_list_source_total.
Goal Logic.True. idtac "AUDIT_END fma_list_source_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fma_list_target_total". exact Logic.I. Qed.
Print Assumptions fma_list_target_total.
Goal Logic.True. idtac "AUDIT_END fma_list_target_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fma_mem_task_related". exact Logic.I. Qed.
Print Assumptions fma_mem_task_related.
Goal Logic.True. idtac "AUDIT_END fma_mem_task_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fma_mem_task_transport". exact Logic.I. Qed.
Print Assumptions fma_mem_task_transport.
Goal Logic.True. idtac "AUDIT_END fma_mem_task_transport". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fma_concrete_related". exact Logic.I. Qed.
Print Assumptions fma_concrete_related.
Goal Logic.True. idtac "AUDIT_END fma_concrete_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fma_generator_valid_related". exact Logic.I. Qed.
Print Assumptions fma_generator_valid_related.
Goal Logic.True. idtac "AUDIT_END fma_generator_valid_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fma_generator_size_related". exact Logic.I. Qed.
Print Assumptions fma_generator_size_related.
Goal Logic.True. idtac "AUDIT_END fma_generator_size_related". exact Logic.I. Qed.
