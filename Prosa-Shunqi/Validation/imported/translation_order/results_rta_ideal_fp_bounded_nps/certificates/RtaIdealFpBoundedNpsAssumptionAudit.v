From FoundationCertificates Require Import
  IdlArrivalsSeqBaseAdapter IdlArrivalsSeqOperations IdlArrivalsSeqCorrespondence IdlArrivalsCorrespondence IdlWorkloadCorrespondence IdlAbstractDefinitionsBaseAdapter IdlServiceBaseAdapter IdlServiceNatBoolOperations IdlAbstractDefinitionsArrivalOperations IdlAbstractDefinitionsClasses IdlAbstractDefinitionsNatBoolOperations IdlAbstractDefinitionsIntervalOperations IdlAbstractDefinitionsOperations IdlAbstractDefinitionsSums IdlAbstractDefinitionsLogical IdlServiceIntervalOperations IdlServiceScheduleOperations IdlAbstractDefinitionsPendingOperations IdlAbstractDefinitionsTaskOperations IdlAbstractDefinitionsBusyIntervalHelpers IdlAbstractRtaHelpers IdlJitterSvcBaseAdapter IdlJitterSvcNatBoolOperations IdlJitterSvcIntervalOperations IdlJitterSvcScheduleOperations IdlJitterSvcJobOperations IdlPreemptionParameterCorrespondence IdlTaskPreemptionParametersCorrespondence IdlIdealAbstractRtaHelpers IdlArrivalSequenceBaseAdapter IdlArrivalSequenceOperations IdlTaskScheduleCorrespondence IdlCurvesCorrespondence IdlRequestBoundFunctionCorrespondence IdlSequentialityCorrespondence IdlServiceOfJobsCorrespondence IdlSupplyScheduleBaseAdapter IdlSupplyScheduleFiniteOperations IdlSupplyScheduleOperations IdlSupplyBaseAdapter IdlSupplyNatBoolOperations IdlSupplyIntervalOperations IdlSupplyCorrespondence IdlIbfTaskHelpers IdlIbfSupplyTaskCorrespondence IdlIbfTaskFullHelpers IdlServiceInversionPredCorrespondence IdlInterferenceCorrespondence IdlPriorityInversionCorrespondence IdlPreemptionTimeCorrespondence IdlStateRel RtaIdealFpBoundedNpsCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN priority_inversion_is_bounded_by_blocking_correspondence". exact Logic.I. Qed.
Print Assumptions priority_inversion_is_bounded_by_blocking_correspondence.
Goal Logic.True. idtac "AUDIT_END priority_inversion_is_bounded_by_blocking_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN priority_inversion_is_bounded_correspondence". exact Logic.I. Qed.
Print Assumptions priority_inversion_is_bounded_correspondence.
Goal Logic.True. idtac "AUDIT_END priority_inversion_is_bounded_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN uniprocessor_response_time_bound_fp_with_bounded_nonpreemptive_segments_correspondence". exact Logic.I. Qed.
Print Assumptions uniprocessor_response_time_bound_fp_with_bounded_nonpreemptive_segments_correspondence.
Goal Logic.True. idtac "AUDIT_END uniprocessor_response_time_bound_fp_with_bounded_nonpreemptive_segments_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rnp_forall_fp". exact Logic.I. Qed.
Print Assumptions rnp_forall_fp.
Goal Logic.True. idtac "AUDIT_END rnp_forall_fp". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rnp_reflexive_task_priorities_rel". exact Logic.I. Qed.
Print Assumptions rnp_reflexive_task_priorities_rel.
Goal Logic.True. idtac "AUDIT_END rnp_reflexive_task_priorities_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rnp_fp_to_jlfp_rel". exact Logic.I. Qed.
Print Assumptions rnp_fp_to_jlfp_rel.
Goal Logic.True. idtac "AUDIT_END rnp_fp_to_jlfp_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rnp_all_jobs_from_taskset_rel". exact Logic.I. Qed.
Print Assumptions rnp_all_jobs_from_taskset_rel.
Goal Logic.True. idtac "AUDIT_END rnp_all_jobs_from_taskset_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rnp_valid_taskset_curve_rel". exact Logic.I. Qed.
Print Assumptions rnp_valid_taskset_curve_rel.
Goal Logic.True. idtac "AUDIT_END rnp_valid_taskset_curve_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rnp_transitive_task_priorities_rel". exact Logic.I. Qed.
Print Assumptions rnp_transitive_task_priorities_rel.
Goal Logic.True. idtac "AUDIT_END rnp_transitive_task_priorities_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rnp_forall_jp". exact Logic.I. Qed.
Print Assumptions rnp_forall_jp.
Goal Logic.True. idtac "AUDIT_END rnp_forall_jp". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rnp_bigmax_canonical". exact Logic.I. Qed.
Print Assumptions rnp_bigmax_canonical.
Goal Logic.True. idtac "AUDIT_END rnp_bigmax_canonical". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rnp_bigmax_related". exact Logic.I. Qed.
Print Assumptions rnp_bigmax_related.
Goal Logic.True. idtac "AUDIT_END rnp_bigmax_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rnp_blocking_bound_rel". exact Logic.I. Qed.
Print Assumptions rnp_blocking_bound_rel.
Goal Logic.True. idtac "AUDIT_END rnp_blocking_bound_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rnp_max_lp_rel". exact Logic.I. Qed.
Print Assumptions rnp_max_lp_rel.
Goal Logic.True. idtac "AUDIT_END rnp_max_lp_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rnp_backlogged_rel". exact Logic.I. Qed.
Print Assumptions rnp_backlogged_rel.
Goal Logic.True. idtac "AUDIT_END rnp_backlogged_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rnp_respects_fp_rel". exact Logic.I. Qed.
Print Assumptions rnp_respects_fp_rel.
Goal Logic.True. idtac "AUDIT_END rnp_respects_fp_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rnp_decide_not". exact Logic.I. Qed.
Print Assumptions rnp_decide_not.
Goal Logic.True. idtac "AUDIT_END rnp_decide_not". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rnp_nat_neqb_related". exact Logic.I. Qed.
Print Assumptions rnp_nat_neqb_related.
Goal Logic.True. idtac "AUDIT_END rnp_nat_neqb_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rnp_bpi_is_in_search_space_rel". exact Logic.I. Qed.
Print Assumptions rnp_bpi_is_in_search_space_rel.
Goal Logic.True. idtac "AUDIT_END rnp_bpi_is_in_search_space_rel". exact Logic.I. Qed.
