From FoundationCertificates Require Import
  IdlArrivalsSeqBaseAdapter IdlArrivalsSeqOperations IdlArrivalsSeqCorrespondence IdlArrivalsCorrespondence IdlWorkloadCorrespondence IdlAbstractDefinitionsBaseAdapter IdlServiceBaseAdapter IdlServiceNatBoolOperations IdlAbstractDefinitionsArrivalOperations IdlAbstractDefinitionsClasses IdlAbstractDefinitionsNatBoolOperations IdlAbstractDefinitionsIntervalOperations IdlAbstractDefinitionsOperations IdlAbstractDefinitionsSums IdlAbstractDefinitionsLogical IdlServiceIntervalOperations IdlServiceScheduleOperations IdlAbstractDefinitionsPendingOperations IdlAbstractDefinitionsTaskOperations IdlAbstractDefinitionsBusyIntervalHelpers IdlAbstractRtaHelpers IdlJitterSvcBaseAdapter IdlJitterSvcNatBoolOperations IdlJitterSvcIntervalOperations IdlJitterSvcScheduleOperations IdlJitterSvcJobOperations IdlPreemptionParameterCorrespondence IdlTaskPreemptionParametersCorrespondence IdlIdealAbstractRtaHelpers IdlArrivalSequenceBaseAdapter IdlArrivalSequenceOperations IdlTaskScheduleCorrespondence IdlCurvesCorrespondence IdlRequestBoundFunctionCorrespondence IdlSequentialityCorrespondence IdlServiceOfJobsCorrespondence IdlSupplyScheduleBaseAdapter IdlSupplyScheduleFiniteOperations IdlSupplyScheduleOperations IdlSupplyBaseAdapter IdlSupplyNatBoolOperations IdlSupplyIntervalOperations IdlSupplyCorrespondence IdlIbfTaskHelpers IdlIbfSupplyTaskCorrespondence IdlIbfTaskFullHelpers IdlServiceInversionPredCorrespondence IdlInterferenceCorrespondence IdlPriorityInversionCorrespondence IdlPreemptionTimeCorrespondence IdlLimitedPreemptiveCorrespondence IdlScheduleLimitedPreemptiveCorrespondence IdlTaskLimitedPreemptiveCorrespondence IdlStateRel RtaIdealFpLimitedPreemptiveCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN uniprocessor_response_time_bound_fp_with_fixed_preemption_points_correspondence". exact Logic.I. Qed.
Print Assumptions uniprocessor_response_time_bound_fp_with_fixed_preemption_points_correspondence.
Goal Logic.True. idtac "AUDIT_END uniprocessor_response_time_bound_fp_with_fixed_preemption_points_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rilp_forall_fp". exact Logic.I. Qed.
Print Assumptions rilp_forall_fp.
Goal Logic.True. idtac "AUDIT_END rilp_forall_fp". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rilp_reflexive_task_priorities_rel". exact Logic.I. Qed.
Print Assumptions rilp_reflexive_task_priorities_rel.
Goal Logic.True. idtac "AUDIT_END rilp_reflexive_task_priorities_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rilp_fp_to_jlfp_rel". exact Logic.I. Qed.
Print Assumptions rilp_fp_to_jlfp_rel.
Goal Logic.True. idtac "AUDIT_END rilp_fp_to_jlfp_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rilp_all_jobs_from_taskset_rel". exact Logic.I. Qed.
Print Assumptions rilp_all_jobs_from_taskset_rel.
Goal Logic.True. idtac "AUDIT_END rilp_all_jobs_from_taskset_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rilp_valid_taskset_curve_rel". exact Logic.I. Qed.
Print Assumptions rilp_valid_taskset_curve_rel.
Goal Logic.True. idtac "AUDIT_END rilp_valid_taskset_curve_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rilp_transitive_task_priorities_rel". exact Logic.I. Qed.
Print Assumptions rilp_transitive_task_priorities_rel.
Goal Logic.True. idtac "AUDIT_END rilp_transitive_task_priorities_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rilp_backlogged_rel". exact Logic.I. Qed.
Print Assumptions rilp_backlogged_rel.
Goal Logic.True. idtac "AUDIT_END rilp_backlogged_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rilp_respects_fp_rel". exact Logic.I. Qed.
Print Assumptions rilp_respects_fp_rel.
Goal Logic.True. idtac "AUDIT_END rilp_respects_fp_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rilp_decide_not". exact Logic.I. Qed.
Print Assumptions rilp_decide_not.
Goal Logic.True. idtac "AUDIT_END rilp_decide_not". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rilp_nat_neqb_related". exact Logic.I. Qed.
Print Assumptions rilp_nat_neqb_related.
Goal Logic.True. idtac "AUDIT_END rilp_nat_neqb_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rilp_bpi_is_in_search_space_rel". exact Logic.I. Qed.
Print Assumptions rilp_bpi_is_in_search_space_rel.
Goal Logic.True. idtac "AUDIT_END rilp_bpi_is_in_search_space_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rilp_sequential_ready_at". exact Logic.I. Qed.
Print Assumptions rilp_sequential_ready_at.
Goal Logic.True. idtac "AUDIT_END rilp_sequential_ready_at". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rilp_forall_jpp". exact Logic.I. Qed.
Print Assumptions rilp_forall_jpp.
Goal Logic.True. idtac "AUDIT_END rilp_forall_jpp". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rilp_forall_tpp". exact Logic.I. Qed.
Print Assumptions rilp_forall_tpp.
Goal Logic.True. idtac "AUDIT_END rilp_forall_tpp". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rilp_job_model_related". exact Logic.I. Qed.
Print Assumptions rilp_job_model_related.
Goal Logic.True. idtac "AUDIT_END rilp_job_model_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rilp_bigmax_canonical". exact Logic.I. Qed.
Print Assumptions rilp_bigmax_canonical.
Goal Logic.True. idtac "AUDIT_END rilp_bigmax_canonical". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rilp_bigmax_related". exact Logic.I. Qed.
Print Assumptions rilp_bigmax_related.
Goal Logic.True. idtac "AUDIT_END rilp_bigmax_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rilp_blocking_bound_rel". exact Logic.I. Qed.
Print Assumptions rilp_blocking_bound_rel.
Goal Logic.True. idtac "AUDIT_END rilp_blocking_bound_rel". exact Logic.I. Qed.
