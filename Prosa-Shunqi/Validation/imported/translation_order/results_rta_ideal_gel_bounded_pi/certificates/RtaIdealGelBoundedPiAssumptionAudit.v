From FoundationCertificates Require Import
  IdlArrivalsSeqBaseAdapter IdlArrivalsSeqOperations IdlArrivalsSeqCorrespondence IdlArrivalsCorrespondence IdlWorkloadCorrespondence IdlAbstractDefinitionsBaseAdapter IdlServiceBaseAdapter IdlServiceNatBoolOperations IdlAbstractDefinitionsArrivalOperations IdlAbstractDefinitionsClasses IdlAbstractDefinitionsNatBoolOperations IdlAbstractDefinitionsIntervalOperations IdlAbstractDefinitionsOperations IdlAbstractDefinitionsSums IdlAbstractDefinitionsLogical IdlServiceIntervalOperations IdlServiceScheduleOperations IdlAbstractDefinitionsPendingOperations IdlAbstractDefinitionsTaskOperations IdlAbstractDefinitionsBusyIntervalHelpers IdlAbstractRtaHelpers IdlJitterSvcBaseAdapter IdlJitterSvcNatBoolOperations IdlJitterSvcIntervalOperations IdlJitterSvcScheduleOperations IdlJitterSvcJobOperations IdlPreemptionParameterCorrespondence IdlTaskPreemptionParametersCorrespondence IdlIdealAbstractRtaHelpers IdlArrivalSequenceBaseAdapter IdlArrivalSequenceOperations IdlTaskScheduleCorrespondence IdlCurvesCorrespondence IdlRequestBoundFunctionCorrespondence IdlSequentialityCorrespondence IdlServiceOfJobsCorrespondence IdlSupplyScheduleBaseAdapter IdlSupplyScheduleFiniteOperations IdlSupplyScheduleOperations IdlSupplyBaseAdapter IdlSupplyNatBoolOperations IdlSupplyIntervalOperations IdlSupplyCorrespondence IdlIbfTaskHelpers IdlIbfSupplyTaskCorrespondence IdlIbfTaskFullHelpers IdlServiceInversionPredCorrespondence IdlInterferenceCorrespondence IdlPriorityInversionCorrespondence IdlPreemptionTimeCorrespondence IdlEdfAthepBoundCorrespondence IdlNatSubCorrespondence IdlPcoBaseAdapter IdlPcoStaticOrder IdlPcoDynamicOrder IdlPriorityCoercionCorrespondence IdlPriorityGelHelpers IdlStateRel RtaIdealGelBoundedPiCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN total_workload_shorten_range_correspondence". exact Logic.I. Qed.
Print Assumptions total_workload_shorten_range_correspondence.
Goal Logic.True. idtac "AUDIT_END total_workload_shorten_range_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sum_of_workloads_is_at_most_bound_on_total_hep_workload_correspondence". exact Logic.I. Qed.
Print Assumptions sum_of_workloads_is_at_most_bound_on_total_hep_workload_correspondence.
Goal Logic.True. idtac "AUDIT_END sum_of_workloads_is_at_most_bound_on_total_hep_workload_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN instantiated_task_interference_is_bounded_correspondence". exact Logic.I. Qed.
Print Assumptions instantiated_task_interference_is_bounded_correspondence.
Goal Logic.True. idtac "AUDIT_END instantiated_task_interference_is_bounded_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN task_rbf_changes_at_correspondence". exact Logic.I. Qed.
Print Assumptions task_rbf_changes_at_correspondence.
Goal Logic.True. idtac "AUDIT_END task_rbf_changes_at_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bound_on_total_hep_workload_changes_at_correspondence". exact Logic.I. Qed.
Print Assumptions bound_on_total_hep_workload_changes_at_correspondence.
Goal Logic.True. idtac "AUDIT_END bound_on_total_hep_workload_changes_at_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN priority_inversion_changes_at_correspondence". exact Logic.I. Qed.
Print Assumptions priority_inversion_changes_at_correspondence.
Goal Logic.True. idtac "AUDIT_END priority_inversion_changes_at_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN is_in_search_space_correspondence". exact Logic.I. Qed.
Print Assumptions is_in_search_space_correspondence.
Goal Logic.True. idtac "AUDIT_END is_in_search_space_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN A_is_in_concrete_search_space_correspondence". exact Logic.I. Qed.
Print Assumptions A_is_in_concrete_search_space_correspondence.
Goal Logic.True. idtac "AUDIT_END A_is_in_concrete_search_space_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN correct_search_space_correspondence". exact Logic.I. Qed.
Print Assumptions correct_search_space_correspondence.
Goal Logic.True. idtac "AUDIT_END correct_search_space_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN uniprocessor_response_time_bound_edf_correspondence". exact Logic.I. Qed.
Print Assumptions uniprocessor_response_time_bound_edf_correspondence.
Goal Logic.True. idtac "AUDIT_END uniprocessor_response_time_bound_edf_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rgel_all_jobs_from_taskset_rel". exact Logic.I. Qed.
Print Assumptions rgel_all_jobs_from_taskset_rel.
Goal Logic.True. idtac "AUDIT_END rgel_all_jobs_from_taskset_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rgel_valid_taskset_curve_rel". exact Logic.I. Qed.
Print Assumptions rgel_valid_taskset_curve_rel.
Goal Logic.True. idtac "AUDIT_END rgel_valid_taskset_curve_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rgel_forall_fun". exact Logic.I. Qed.
Print Assumptions rgel_forall_fun.
Goal Logic.True. idtac "AUDIT_END rgel_forall_fun". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rgel_basic_ready_at". exact Logic.I. Qed.
Print Assumptions rgel_basic_ready_at.
Goal Logic.True. idtac "AUDIT_END rgel_basic_ready_at". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rgel_backlogged_rel". exact Logic.I. Qed.
Print Assumptions rgel_backlogged_rel.
Goal Logic.True. idtac "AUDIT_END rgel_backlogged_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rgel_respects_jlfp_rel". exact Logic.I. Qed.
Print Assumptions rgel_respects_jlfp_rel.
Goal Logic.True. idtac "AUDIT_END rgel_respects_jlfp_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rgel_decide_not". exact Logic.I. Qed.
Print Assumptions rgel_decide_not.
Goal Logic.True. idtac "AUDIT_END rgel_decide_not". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rgel_nat_neqb_related". exact Logic.I. Qed.
Print Assumptions rgel_nat_neqb_related.
Goal Logic.True. idtac "AUDIT_END rgel_nat_neqb_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rgel_has_canonical". exact Logic.I. Qed.
Print Assumptions rgel_has_canonical.
Goal Logic.True. idtac "AUDIT_END rgel_has_canonical". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rgel_has_related". exact Logic.I. Qed.
Print Assumptions rgel_has_related.
Goal Logic.True. idtac "AUDIT_END rgel_has_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rgel_gel_rel". exact Logic.I. Qed.
Print Assumptions rgel_gel_rel.
Goal Logic.True. idtac "AUDIT_END rgel_gel_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rgel_subz_pp_le". exact Logic.I. Qed.
Print Assumptions rgel_subz_pp_le.
Goal Logic.True. idtac "AUDIT_END rgel_subz_pp_le". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rgel_subz_pp_gt". exact Logic.I. Qed.
Print Assumptions rgel_subz_pp_gt.
Goal Logic.True. idtac "AUDIT_END rgel_subz_pp_gt". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rgel_subz_pn". exact Logic.I. Qed.
Print Assumptions rgel_subz_pn.
Goal Logic.True. idtac "AUDIT_END rgel_subz_pn". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rgel_subz_np". exact Logic.I. Qed.
Print Assumptions rgel_subz_np.
Goal Logic.True. idtac "AUDIT_END rgel_subz_np". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rgel_subz_nn_le". exact Logic.I. Qed.
Print Assumptions rgel_subz_nn_le.
Goal Logic.True. idtac "AUDIT_END rgel_subz_nn_le". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rgel_subz_nn_gt". exact Logic.I. Qed.
Print Assumptions rgel_subz_nn_gt.
Goal Logic.True. idtac "AUDIT_END rgel_subz_nn_gt". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rgel_absmax_p". exact Logic.I. Qed.
Print Assumptions rgel_absmax_p.
Goal Logic.True. idtac "AUDIT_END rgel_absmax_p". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rgel_absmax_n". exact Logic.I. Qed.
Print Assumptions rgel_absmax_n.
Goal Logic.True. idtac "AUDIT_END rgel_absmax_n". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rgel_sub1_related". exact Logic.I. Qed.
Print Assumptions rgel_sub1_related.
Goal Logic.True. idtac "AUDIT_END rgel_sub1_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rgel_add1_related". exact Logic.I. Qed.
Print Assumptions rgel_add1_related.
Goal Logic.True. idtac "AUDIT_END rgel_add1_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rgel_sub_canonical". exact Logic.I. Qed.
Print Assumptions rgel_sub_canonical.
Goal Logic.True. idtac "AUDIT_END rgel_sub_canonical". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rgel_sub_related". exact Logic.I. Qed.
Print Assumptions rgel_sub_related.
Goal Logic.True. idtac "AUDIT_END rgel_sub_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rgel_absmax_canonical". exact Logic.I. Qed.
Print Assumptions rgel_absmax_canonical.
Goal Logic.True. idtac "AUDIT_END rgel_absmax_canonical". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rgel_absmax_related". exact Logic.I. Qed.
Print Assumptions rgel_absmax_related.
Goal Logic.True. idtac "AUDIT_END rgel_absmax_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rgel_int_neq_le". exact Logic.I. Qed.
Print Assumptions rgel_int_neq_le.
Goal Logic.True. idtac "AUDIT_END rgel_int_neq_le". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rgel_int_neq_related". exact Logic.I. Qed.
Print Assumptions rgel_int_neq_related.
Goal Logic.True. idtac "AUDIT_END rgel_int_neq_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rgel_cast_related". exact Logic.I. Qed.
Print Assumptions rgel_cast_related.
Goal Logic.True. idtac "AUDIT_END rgel_cast_related". exact Logic.I. Qed.
