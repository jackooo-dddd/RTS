From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence WorkloadCorrespondence CurvesCorrespondence RequestBoundFunctionCorrespondence WorkloadBoundedCorrespondence FactsRbfCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN task_workload_between_bounded_correspondence". exact Logic.I. Qed.
Print Assumptions task_workload_between_bounded_correspondence.
Goal Logic.True. idtac "AUDIT_END task_workload_between_bounded_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rbf_spec_correspondence". exact Logic.I. Qed.
Print Assumptions rbf_spec_correspondence.
Goal Logic.True. idtac "AUDIT_END rbf_spec_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rbf_spec'_correspondence". exact Logic.I. Qed.
Print Assumptions rbf_spec'_correspondence.
Goal Logic.True. idtac "AUDIT_END rbf_spec'_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN total_workload_le_total_rbf_correspondence". exact Logic.I. Qed.
Print Assumptions total_workload_le_total_rbf_correspondence.
Goal Logic.True. idtac "AUDIT_END total_workload_le_total_rbf_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN workload_of_jobs_bounded_correspondence". exact Logic.I. Qed.
Print Assumptions workload_of_jobs_bounded_correspondence.
Goal Logic.True. idtac "AUDIT_END workload_of_jobs_bounded_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN athep_workload_le_total_ohep_rbf_correspondence". exact Logic.I. Qed.
Print Assumptions athep_workload_le_total_ohep_rbf_correspondence.
Goal Logic.True. idtac "AUDIT_END athep_workload_le_total_ohep_rbf_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN hep_workload_le_total_hep_rbf_correspondence". exact Logic.I. Qed.
Print Assumptions hep_workload_le_total_hep_rbf_correspondence.
Goal Logic.True. idtac "AUDIT_END hep_workload_le_total_hep_rbf_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN hep_workload_le_total_rbf_correspondence". exact Logic.I. Qed.
Print Assumptions hep_workload_le_total_rbf_correspondence.
Goal Logic.True. idtac "AUDIT_END hep_workload_le_total_rbf_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN task_rbf_0_zero_correspondence". exact Logic.I. Qed.
Print Assumptions task_rbf_0_zero_correspondence.
Goal Logic.True. idtac "AUDIT_END task_rbf_0_zero_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN task_rbf_monotone_correspondence". exact Logic.I. Qed.
Print Assumptions task_rbf_monotone_correspondence.
Goal Logic.True. idtac "AUDIT_END task_rbf_monotone_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN task_rbf_1_ge_task_cost_correspondence". exact Logic.I. Qed.
Print Assumptions task_rbf_1_ge_task_cost_correspondence.
Goal Logic.True. idtac "AUDIT_END task_rbf_1_ge_task_cost_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN task_rbf_ge_task_cost_correspondence". exact Logic.I. Qed.
Print Assumptions task_rbf_ge_task_cost_correspondence.
Goal Logic.True. idtac "AUDIT_END task_rbf_ge_task_cost_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN task_rbf_epsilon_gt_0_correspondence". exact Logic.I. Qed.
Print Assumptions task_rbf_epsilon_gt_0_correspondence.
Goal Logic.True. idtac "AUDIT_END task_rbf_epsilon_gt_0_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN task_cost_le_sum_rbf_correspondence". exact Logic.I. Qed.
Print Assumptions task_cost_le_sum_rbf_correspondence.
Goal Logic.True. idtac "AUDIT_END task_cost_le_sum_rbf_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN total_rbf_monotone_correspondence". exact Logic.I. Qed.
Print Assumptions total_rbf_monotone_correspondence.
Goal Logic.True. idtac "AUDIT_END total_rbf_monotone_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN total_hep_rbf_monotone_correspondence". exact Logic.I. Qed.
Print Assumptions total_hep_rbf_monotone_correspondence.
Goal Logic.True. idtac "AUDIT_END total_hep_rbf_monotone_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN total_ohep_rbf_monotone_correspondence". exact Logic.I. Qed.
Print Assumptions total_ohep_rbf_monotone_correspondence.
Goal Logic.True. idtac "AUDIT_END total_ohep_rbf_monotone_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pathological_rbf_response_time_bound_correspondence". exact Logic.I. Qed.
Print Assumptions pathological_rbf_response_time_bound_correspondence.
Goal Logic.True. idtac "AUDIT_END pathological_rbf_response_time_bound_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pathological_total_hep_rbf_response_time_bound_correspondence". exact Logic.I. Qed.
Print Assumptions pathological_total_hep_rbf_response_time_bound_correspondence.
Goal Logic.True. idtac "AUDIT_END pathological_total_hep_rbf_response_time_bound_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pathological_total_hep_rbf_any_bound_correspondence". exact Logic.I. Qed.
Print Assumptions pathological_total_hep_rbf_any_bound_correspondence.
Goal Logic.True. idtac "AUDIT_END pathological_total_hep_rbf_any_bound_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN hep_rbf_taskwise_partitioning_correspondence". exact Logic.I. Qed.
Print Assumptions hep_rbf_taskwise_partitioning_correspondence.
Goal Logic.True. idtac "AUDIT_END hep_rbf_taskwise_partitioning_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN split_hep_rbf_correspondence". exact Logic.I. Qed.
Print Assumptions split_hep_rbf_correspondence.
Goal Logic.True. idtac "AUDIT_END split_hep_rbf_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN split_hep_rbf_weaken_correspondence". exact Logic.I. Qed.
Print Assumptions split_hep_rbf_weaken_correspondence.
Goal Logic.True. idtac "AUDIT_END split_hep_rbf_weaken_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN total_ohep_rbf0_correspondence". exact Logic.I. Qed.
Print Assumptions total_ohep_rbf0_correspondence.
Goal Logic.True. idtac "AUDIT_END total_ohep_rbf0_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ohep_workload_le_rbf_correspondence". exact Logic.I. Qed.
Print Assumptions ohep_workload_le_rbf_correspondence.
Goal Logic.True. idtac "AUDIT_END ohep_workload_le_rbf_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN task_rbf_without_job_under_analysis_from_arrival_correspondence". exact Logic.I. Qed.
Print Assumptions task_rbf_without_job_under_analysis_from_arrival_correspondence.
Goal Logic.True. idtac "AUDIT_END task_rbf_without_job_under_analysis_from_arrival_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN task_rbf_without_job_under_analysis_correspondence". exact Logic.I. Qed.
Print Assumptions task_rbf_without_job_under_analysis_correspondence.
Goal Logic.True. idtac "AUDIT_END task_rbf_without_job_under_analysis_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frbf_forall_cover_sprop". exact Logic.I. Qed.
Print Assumptions frbf_forall_cover_sprop.
Goal Logic.True. idtac "AUDIT_END frbf_forall_cover_sprop". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frbf_forall_cover_type". exact Logic.I. Qed.
Print Assumptions frbf_forall_cover_type.
Goal Logic.True. idtac "AUDIT_END frbf_forall_cover_type". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frbf_lean_transport". exact Logic.I. Qed.
Print Assumptions frbf_lean_transport.
Goal Logic.True. idtac "AUDIT_END frbf_lean_transport". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frbf_nat_input". exact Logic.I. Qed.
Print Assumptions frbf_nat_input.
Goal Logic.True. idtac "AUDIT_END frbf_nat_input". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frbf_decide_eq_related". exact Logic.I. Qed.
Print Assumptions frbf_decide_eq_related.
Goal Logic.True. idtac "AUDIT_END frbf_decide_eq_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frbf_bool_rel_true". exact Logic.I. Qed.
Print Assumptions frbf_bool_rel_true.
Goal Logic.True. idtac "AUDIT_END frbf_bool_rel_true". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frbf_bool_false_of_rocq". exact Logic.I. Qed.
Print Assumptions frbf_bool_false_of_rocq.
Goal Logic.True. idtac "AUDIT_END frbf_bool_false_of_rocq". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frbf_map_values_canonical". exact Logic.I. Qed.
Print Assumptions frbf_map_values_canonical.
Goal Logic.True. idtac "AUDIT_END frbf_map_values_canonical". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frbf_ar_svc_list_eq". exact Logic.I. Qed.
Print Assumptions frbf_ar_svc_list_eq.
Goal Logic.True. idtac "AUDIT_END frbf_ar_svc_list_eq". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frbf_monotone_related". exact Logic.I. Qed.
Print Assumptions frbf_monotone_related.
Goal Logic.True. idtac "AUDIT_END frbf_monotone_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frbf_psr_sched_to_target_rel". exact Logic.I. Qed.
Print Assumptions frbf_psr_sched_to_target_rel.
Goal Logic.True. idtac "AUDIT_END frbf_psr_sched_to_target_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frbf_psr_sched_to_source_rel". exact Logic.I. Qed.
Print Assumptions frbf_psr_sched_to_source_rel.
Goal Logic.True. idtac "AUDIT_END frbf_psr_sched_to_source_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frbf_psr_service_at_related". exact Logic.I. Qed.
Print Assumptions frbf_psr_service_at_related.
Goal Logic.True. idtac "AUDIT_END frbf_psr_service_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frbf_psr_service_related". exact Logic.I. Qed.
Print Assumptions frbf_psr_service_related.
Goal Logic.True. idtac "AUDIT_END frbf_psr_service_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frbf_enum_nodup". exact Logic.I. Qed.
Print Assumptions frbf_enum_nodup.
Goal Logic.True. idtac "AUDIT_END frbf_enum_nodup". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frbf_enum_complete". exact Logic.I. Qed.
Print Assumptions frbf_enum_complete.
Goal Logic.True. idtac "AUDIT_END frbf_enum_complete". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frbf_law_le". exact Logic.I. Qed.
Print Assumptions frbf_law_le.
Goal Logic.True. idtac "AUDIT_END frbf_law_le". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frbf_law_zero". exact Logic.I. Qed.
Print Assumptions frbf_law_zero.
Goal Logic.True. idtac "AUDIT_END frbf_law_zero". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frbf_to_target_service_in". exact Logic.I. Qed.
Print Assumptions frbf_to_target_service_in.
Goal Logic.True. idtac "AUDIT_END frbf_to_target_service_in". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frbf_to_target_supply_in". exact Logic.I. Qed.
Print Assumptions frbf_to_target_supply_in.
Goal Logic.True. idtac "AUDIT_END frbf_to_target_supply_in". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frbf_core_eqP". exact Logic.I. Qed.
Print Assumptions frbf_core_eqP.
Goal Logic.True. idtac "AUDIT_END frbf_core_eqP". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frbf_core_list_rel". exact Logic.I. Qed.
Print Assumptions frbf_core_list_rel.
Goal Logic.True. idtac "AUDIT_END frbf_core_list_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frbf_core_list_uniq". exact Logic.I. Qed.
Print Assumptions frbf_core_list_uniq.
Goal Logic.True. idtac "AUDIT_END frbf_core_list_uniq". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frbf_core_list_complete". exact Logic.I. Qed.
Print Assumptions frbf_core_list_complete.
Goal Logic.True. idtac "AUDIT_END frbf_core_list_complete". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frbf_core_enum_map". exact Logic.I. Qed.
Print Assumptions frbf_core_enum_map.
Goal Logic.True. idtac "AUDIT_END frbf_core_enum_map". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frbf_src_law_le". exact Logic.I. Qed.
Print Assumptions frbf_src_law_le.
Goal Logic.True. idtac "AUDIT_END frbf_src_law_le". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frbf_src_law_zero". exact Logic.I. Qed.
Print Assumptions frbf_src_law_zero.
Goal Logic.True. idtac "AUDIT_END frbf_src_law_zero". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frbf_core_enumeration_rel". exact Logic.I. Qed.
Print Assumptions frbf_core_enumeration_rel.
Goal Logic.True. idtac "AUDIT_END frbf_core_enumeration_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frbf_to_source_service_in". exact Logic.I. Qed.
Print Assumptions frbf_to_source_service_in.
Goal Logic.True. idtac "AUDIT_END frbf_to_source_service_in". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frbf_to_source_supply_in". exact Logic.I. Qed.
Print Assumptions frbf_to_source_supply_in.
Goal Logic.True. idtac "AUDIT_END frbf_to_source_supply_in". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frbf_list_to_target_rel". exact Logic.I. Qed.
Print Assumptions frbf_list_to_target_rel.
Goal Logic.True. idtac "AUDIT_END frbf_list_to_target_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frbf_list_to_source_rel". exact Logic.I. Qed.
Print Assumptions frbf_list_to_source_rel.
Goal Logic.True. idtac "AUDIT_END frbf_list_to_source_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frbf_pred_to_source_rel". exact Logic.I. Qed.
Print Assumptions frbf_pred_to_source_rel.
Goal Logic.True. idtac "AUDIT_END frbf_pred_to_source_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frbf_fp_to_target_rel". exact Logic.I. Qed.
Print Assumptions frbf_fp_to_target_rel.
Goal Logic.True. idtac "AUDIT_END frbf_fp_to_target_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frbf_fp_to_source_rel". exact Logic.I. Qed.
Print Assumptions frbf_fp_to_source_rel.
Goal Logic.True. idtac "AUDIT_END frbf_fp_to_source_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frbf_jlfp_to_target_rel". exact Logic.I. Qed.
Print Assumptions frbf_jlfp_to_target_rel.
Goal Logic.True. idtac "AUDIT_END frbf_jlfp_to_target_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frbf_jlfp_to_source_rel". exact Logic.I. Qed.
Print Assumptions frbf_jlfp_to_source_rel.
Goal Logic.True. idtac "AUDIT_END frbf_jlfp_to_source_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frbf_job_of_task_related". exact Logic.I. Qed.
Print Assumptions frbf_job_of_task_related.
Goal Logic.True. idtac "AUDIT_END frbf_job_of_task_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frbf_task_cost_of_job_related". exact Logic.I. Qed.
Print Assumptions frbf_task_cost_of_job_related.
Goal Logic.True. idtac "AUDIT_END frbf_task_cost_of_job_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frbf_valid_job_costs_related". exact Logic.I. Qed.
Print Assumptions frbf_valid_job_costs_related.
Goal Logic.True. idtac "AUDIT_END frbf_valid_job_costs_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frbf_all_jobs_from_taskset_related". exact Logic.I. Qed.
Print Assumptions frbf_all_jobs_from_taskset_related.
Goal Logic.True. idtac "AUDIT_END frbf_all_jobs_from_taskset_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frbf_hep_task_jobs". exact Logic.I. Qed.
Print Assumptions frbf_hep_task_jobs.
Goal Logic.True. idtac "AUDIT_END frbf_hep_task_jobs". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frbf_reflexive_task_related". exact Logic.I. Qed.
Print Assumptions frbf_reflexive_task_related.
Goal Logic.True. idtac "AUDIT_END frbf_reflexive_task_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frbf_max1_positive_related". exact Logic.I. Qed.
Print Assumptions frbf_max1_positive_related.
Goal Logic.True. idtac "AUDIT_END frbf_max1_positive_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frbf_task_response_time_bound_related". exact Logic.I. Qed.
Print Assumptions frbf_task_response_time_bound_related.
Goal Logic.True. idtac "AUDIT_END frbf_task_response_time_bound_related". exact Logic.I. Qed.
