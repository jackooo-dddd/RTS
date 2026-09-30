From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence WcTransCorrespondence FactsWcCorrectnessCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN is_work_conserving_at_correspondence". exact Logic.I. Qed.
Print Assumptions is_work_conserving_at_correspondence.
Goal Logic.True. idtac "AUDIT_END is_work_conserving_at_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN swap_candidate_is_in_future_correspondence". exact Logic.I. Qed.
Print Assumptions swap_candidate_is_in_future_correspondence.
Goal Logic.True. idtac "AUDIT_END swap_candidate_is_in_future_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsc_respects_has_arrived_correspondence". exact Logic.I. Qed.
Print Assumptions fsc_respects_has_arrived_correspondence.
Goal Logic.True. idtac "AUDIT_END fsc_respects_has_arrived_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN swap_jobs_must_arrive_to_execute_correspondence". exact Logic.I. Qed.
Print Assumptions swap_jobs_must_arrive_to_execute_correspondence.
Goal Logic.True. idtac "AUDIT_END swap_jobs_must_arrive_to_execute_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsc_jobs_must_be_ready_to_execute_correspondence". exact Logic.I. Qed.
Print Assumptions fsc_jobs_must_be_ready_to_execute_correspondence.
Goal Logic.True. idtac "AUDIT_END fsc_jobs_must_be_ready_to_execute_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN mwa_service_bound_correspondence". exact Logic.I. Qed.
Print Assumptions mwa_service_bound_correspondence.
Goal Logic.True. idtac "AUDIT_END mwa_service_bound_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN mwa_ready_job_also_ready_in_original_schedule_correspondence". exact Logic.I. Qed.
Print Assumptions mwa_ready_job_also_ready_in_original_schedule_correspondence.
Goal Logic.True. idtac "AUDIT_END mwa_ready_job_also_ready_in_original_schedule_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN max_dl_is_greatest_dl_correspondence". exact Logic.I. Qed.
Print Assumptions max_dl_is_greatest_dl_correspondence.
Goal Logic.True. idtac "AUDIT_END max_dl_is_greatest_dl_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN order_correspondence". exact Logic.I. Qed.
Print Assumptions order_correspondence.
Goal Logic.True. idtac "AUDIT_END order_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN search_result_correspondence". exact Logic.I. Qed.
Print Assumptions search_result_correspondence.
Goal Logic.True. idtac "AUDIT_END search_result_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN make_wc_at_case_result_found_correspondence". exact Logic.I. Qed.
Print Assumptions make_wc_at_case_result_found_correspondence.
Goal Logic.True. idtac "AUDIT_END make_wc_at_case_result_found_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN no_relevant_state_in_range_correspondence". exact Logic.I. Qed.
Print Assumptions no_relevant_state_in_range_correspondence.
Goal Logic.True. idtac "AUDIT_END no_relevant_state_in_range_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_of_j_is_less_than_cost_correspondence". exact Logic.I. Qed.
Print Assumptions service_of_j_is_less_than_cost_correspondence.
Goal Logic.True. idtac "AUDIT_END service_of_j_is_less_than_cost_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN t_is_less_than_deadline_of_j_correspondence". exact Logic.I. Qed.
Print Assumptions t_is_less_than_deadline_of_j_correspondence.
Goal Logic.True. idtac "AUDIT_END t_is_less_than_deadline_of_j_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN equal_service_t_max_dl_correspondence". exact Logic.I. Qed.
Print Assumptions equal_service_t_max_dl_correspondence.
Goal Logic.True. idtac "AUDIT_END equal_service_t_max_dl_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN j_misses_deadline_correspondence". exact Logic.I. Qed.
Print Assumptions j_misses_deadline_correspondence.
Goal Logic.True. idtac "AUDIT_END j_misses_deadline_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN make_wc_at_case_result_none_correspondence". exact Logic.I. Qed.
Print Assumptions make_wc_at_case_result_none_correspondence.
Goal Logic.True. idtac "AUDIT_END make_wc_at_case_result_none_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN mwa_finds_ready_jobs_correspondence". exact Logic.I. Qed.
Print Assumptions mwa_finds_ready_jobs_correspondence.
Goal Logic.True. idtac "AUDIT_END mwa_finds_ready_jobs_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN mwa_establishes_wc_correspondence". exact Logic.I. Qed.
Print Assumptions mwa_establishes_wc_correspondence.
Goal Logic.True. idtac "AUDIT_END mwa_establishes_wc_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN mwa_jobs_come_from_arrival_sequence_correspondence". exact Logic.I. Qed.
Print Assumptions mwa_jobs_come_from_arrival_sequence_correspondence.
Goal Logic.True. idtac "AUDIT_END mwa_jobs_come_from_arrival_sequence_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN mwa_jobs_must_be_ready_to_execute_correspondence". exact Logic.I. Qed.
Print Assumptions mwa_jobs_must_be_ready_to_execute_correspondence.
Goal Logic.True. idtac "AUDIT_END mwa_jobs_must_be_ready_to_execute_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN mwa_all_deadlines_of_arrivals_met_correspondence". exact Logic.I. Qed.
Print Assumptions mwa_all_deadlines_of_arrivals_met_correspondence.
Goal Logic.True. idtac "AUDIT_END mwa_all_deadlines_of_arrivals_met_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wc_transform_prefix_inclusion_correspondence". exact Logic.I. Qed.
Print Assumptions wc_transform_prefix_inclusion_correspondence.
Goal Logic.True. idtac "AUDIT_END wc_transform_prefix_inclusion_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wc_prefix_service_bound_correspondence". exact Logic.I. Qed.
Print Assumptions wc_prefix_service_bound_correspondence.
Goal Logic.True. idtac "AUDIT_END wc_prefix_service_bound_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wc_prefix_job_meets_deadline_correspondence". exact Logic.I. Qed.
Print Assumptions wc_prefix_job_meets_deadline_correspondence.
Goal Logic.True. idtac "AUDIT_END wc_prefix_job_meets_deadline_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wc_prefix_jobs_come_from_arrival_sequence_correspondence". exact Logic.I. Qed.
Print Assumptions wc_prefix_jobs_come_from_arrival_sequence_correspondence.
Goal Logic.True. idtac "AUDIT_END wc_prefix_jobs_come_from_arrival_sequence_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wc_prefix_jobs_must_be_ready_to_execute_correspondence". exact Logic.I. Qed.
Print Assumptions wc_prefix_jobs_must_be_ready_to_execute_correspondence.
Goal Logic.True. idtac "AUDIT_END wc_prefix_jobs_must_be_ready_to_execute_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wc_jobs_come_from_arrival_sequence_correspondence". exact Logic.I. Qed.
Print Assumptions wc_jobs_come_from_arrival_sequence_correspondence.
Goal Logic.True. idtac "AUDIT_END wc_jobs_come_from_arrival_sequence_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wc_jobs_must_be_ready_to_execute_correspondence". exact Logic.I. Qed.
Print Assumptions wc_jobs_must_be_ready_to_execute_correspondence.
Goal Logic.True. idtac "AUDIT_END wc_jobs_must_be_ready_to_execute_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wc_all_deadlines_of_arrivals_met_correspondence". exact Logic.I. Qed.
Print Assumptions wc_all_deadlines_of_arrivals_met_correspondence.
Goal Logic.True. idtac "AUDIT_END wc_all_deadlines_of_arrivals_met_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wc_is_work_conserving_at_correspondence". exact Logic.I. Qed.
Print Assumptions wc_is_work_conserving_at_correspondence.
Goal Logic.True. idtac "AUDIT_END wc_is_work_conserving_at_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wc_is_work_conserving_correspondence". exact Logic.I. Qed.
Print Assumptions wc_is_work_conserving_correspondence.
Goal Logic.True. idtac "AUDIT_END wc_is_work_conserving_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wc_transform_correctness_correspondence". exact Logic.I. Qed.
Print Assumptions wc_transform_correctness_correspondence.
Goal Logic.True. idtac "AUDIT_END wc_transform_correctness_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wcc_forall_cover". exact Logic.I. Qed.
Print Assumptions wcc_forall_cover.
Goal Logic.True. idtac "AUDIT_END wcc_forall_cover". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wcc_exists_identity_correspondence". exact Logic.I. Qed.
Print Assumptions wcc_exists_identity_correspondence.
Goal Logic.True. idtac "AUDIT_END wcc_exists_identity_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wcc_false_correspondence". exact Logic.I. Qed.
Print Assumptions wcc_false_correspondence.
Goal Logic.True. idtac "AUDIT_END wcc_false_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wcc_opt_source_roundtrip". exact Logic.I. Qed.
Print Assumptions wcc_opt_source_roundtrip.
Goal Logic.True. idtac "AUDIT_END wcc_opt_source_roundtrip". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wcc_opt_target_roundtrip". exact Logic.I. Qed.
Print Assumptions wcc_opt_target_roundtrip.
Goal Logic.True. idtac "AUDIT_END wcc_opt_target_roundtrip". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wcc_opt_rel_canonical". exact Logic.I. Qed.
Print Assumptions wcc_opt_rel_canonical.
Goal Logic.True. idtac "AUDIT_END wcc_opt_rel_canonical". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wcc_opt_eq_correspondence". exact Logic.I. Qed.
Print Assumptions wcc_opt_eq_correspondence.
Goal Logic.True. idtac "AUDIT_END wcc_opt_eq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wcc_option_some_eq_correspondence". exact Logic.I. Qed.
Print Assumptions wcc_option_some_eq_correspondence.
Goal Logic.True. idtac "AUDIT_END wcc_option_some_eq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wcc_option_some_eq_rel". exact Logic.I. Qed.
Print Assumptions wcc_option_some_eq_rel.
Goal Logic.True. idtac "AUDIT_END wcc_option_some_eq_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wcc_option_none_eq_related". exact Logic.I. Qed.
Print Assumptions wcc_option_none_eq_related.
Goal Logic.True. idtac "AUDIT_END wcc_option_none_eq_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wcc_optnat_roundtrip". exact Logic.I. Qed.
Print Assumptions wcc_optnat_roundtrip.
Goal Logic.True. idtac "AUDIT_END wcc_optnat_roundtrip". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wcc_optnat_some_eq". exact Logic.I. Qed.
Print Assumptions wcc_optnat_some_eq.
Goal Logic.True. idtac "AUDIT_END wcc_optnat_some_eq". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wcc_optnat_none_eq". exact Logic.I. Qed.
Print Assumptions wcc_optnat_none_eq.
Goal Logic.True. idtac "AUDIT_END wcc_optnat_none_eq". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wcc_src_scheduled_on". exact Logic.I. Qed.
Print Assumptions wcc_src_scheduled_on.
Goal Logic.True. idtac "AUDIT_END wcc_src_scheduled_on". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wcc_src_scheduled_in". exact Logic.I. Qed.
Print Assumptions wcc_src_scheduled_in.
Goal Logic.True. idtac "AUDIT_END wcc_src_scheduled_in". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wcc_src_service_in". exact Logic.I. Qed.
Print Assumptions wcc_src_service_in.
Goal Logic.True. idtac "AUDIT_END wcc_src_service_in". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wcc_scheduled_in_related". exact Logic.I. Qed.
Print Assumptions wcc_scheduled_in_related.
Goal Logic.True. idtac "AUDIT_END wcc_scheduled_in_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wcc_decide_state_related". exact Logic.I. Qed.
Print Assumptions wcc_decide_state_related.
Goal Logic.True. idtac "AUDIT_END wcc_decide_state_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wcc_service_on_related". exact Logic.I. Qed.
Print Assumptions wcc_service_on_related.
Goal Logic.True. idtac "AUDIT_END wcc_service_on_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wcc_service_in_related". exact Logic.I. Qed.
Print Assumptions wcc_service_in_related.
Goal Logic.True. idtac "AUDIT_END wcc_service_in_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wcc_sched_to_target_rel". exact Logic.I. Qed.
Print Assumptions wcc_sched_to_target_rel.
Goal Logic.True. idtac "AUDIT_END wcc_sched_to_target_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wcc_sched_to_source_rel". exact Logic.I. Qed.
Print Assumptions wcc_sched_to_source_rel.
Goal Logic.True. idtac "AUDIT_END wcc_sched_to_source_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wcc_forall_sched". exact Logic.I. Qed.
Print Assumptions wcc_forall_sched.
Goal Logic.True. idtac "AUDIT_END wcc_forall_sched". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wcc_scheduled_at_related". exact Logic.I. Qed.
Print Assumptions wcc_scheduled_at_related.
Goal Logic.True. idtac "AUDIT_END wcc_scheduled_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wcc_sched_at". exact Logic.I. Qed.
Print Assumptions wcc_sched_at.
Goal Logic.True. idtac "AUDIT_END wcc_sched_at". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wcc_service_at_fun". exact Logic.I. Qed.
Print Assumptions wcc_service_at_fun.
Goal Logic.True. idtac "AUDIT_END wcc_service_at_fun". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wcc_service_related". exact Logic.I. Qed.
Print Assumptions wcc_service_related.
Goal Logic.True. idtac "AUDIT_END wcc_service_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wcc_idle_related". exact Logic.I. Qed.
Print Assumptions wcc_idle_related.
Goal Logic.True. idtac "AUDIT_END wcc_idle_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wcc_maxdl". exact Logic.I. Qed.
Print Assumptions wcc_maxdl.
Goal Logic.True. idtac "AUDIT_END wcc_maxdl". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wcc_fsc". exact Logic.I. Qed.
Print Assumptions wcc_fsc.
Goal Logic.True. idtac "AUDIT_END wcc_fsc". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wcc_mwa". exact Logic.I. Qed.
Print Assumptions wcc_mwa.
Goal Logic.True. idtac "AUDIT_END wcc_mwa". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wcc_prefix". exact Logic.I. Qed.
Print Assumptions wcc_prefix.
Goal Logic.True. idtac "AUDIT_END wcc_prefix". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wcc_transform". exact Logic.I. Qed.
Print Assumptions wcc_transform.
Goal Logic.True. idtac "AUDIT_END wcc_transform". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wcc_swapped". exact Logic.I. Qed.
Print Assumptions wcc_swapped.
Goal Logic.True. idtac "AUDIT_END wcc_swapped". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wcc_pending_related". exact Logic.I. Qed.
Print Assumptions wcc_pending_related.
Goal Logic.True. idtac "AUDIT_END wcc_pending_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wcc_ready_related". exact Logic.I. Qed.
Print Assumptions wcc_ready_related.
Goal Logic.True. idtac "AUDIT_END wcc_ready_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wcc_ready". exact Logic.I. Qed.
Print Assumptions wcc_ready.
Goal Logic.True. idtac "AUDIT_END wcc_ready". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wcc_jmae_rel". exact Logic.I. Qed.
Print Assumptions wcc_jmae_rel.
Goal Logic.True. idtac "AUDIT_END wcc_jmae_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wcc_jmbr_rel". exact Logic.I. Qed.
Print Assumptions wcc_jmbr_rel.
Goal Logic.True. idtac "AUDIT_END wcc_jmbr_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wcc_jcf_rel". exact Logic.I. Qed.
Print Assumptions wcc_jcf_rel.
Goal Logic.True. idtac "AUDIT_END wcc_jcf_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wcc_valid_rel". exact Logic.I. Qed.
Print Assumptions wcc_valid_rel.
Goal Logic.True. idtac "AUDIT_END wcc_valid_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wcc_meets_rel". exact Logic.I. Qed.
Print Assumptions wcc_meets_rel.
Goal Logic.True. idtac "AUDIT_END wcc_meets_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wcc_doa_rel". exact Logic.I. Qed.
Print Assumptions wcc_doa_rel.
Goal Logic.True. idtac "AUDIT_END wcc_doa_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wcc_wc_rel". exact Logic.I. Qed.
Print Assumptions wcc_wc_rel.
Goal Logic.True. idtac "AUDIT_END wcc_wc_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wcc_case_prefix". exact Logic.I. Qed.
Print Assumptions wcc_case_prefix.
Goal Logic.True. idtac "AUDIT_END wcc_case_prefix". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wcc_none_prefix". exact Logic.I. Qed.
Print Assumptions wcc_none_prefix.
Goal Logic.True. idtac "AUDIT_END wcc_none_prefix". exact Logic.I. Qed.
