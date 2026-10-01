From FoundationCertificates Require Import
  IdlArrivalsSeqBaseAdapter IdlArrivalsSeqOperations IdlArrivalsSeqCorrespondence IdlArrivalsCorrespondence IdlWorkloadCorrespondence IdlAbstractDefinitionsBaseAdapter IdlServiceBaseAdapter IdlServiceNatBoolOperations IdlAbstractDefinitionsArrivalOperations IdlAbstractDefinitionsClasses IdlAbstractDefinitionsNatBoolOperations IdlAbstractDefinitionsIntervalOperations IdlAbstractDefinitionsOperations IdlAbstractDefinitionsSums IdlAbstractDefinitionsLogical IdlServiceIntervalOperations IdlServiceScheduleOperations IdlAbstractDefinitionsPendingOperations IdlAbstractDefinitionsTaskOperations IdlAbstractDefinitionsBusyIntervalHelpers IdlAbstractRtaHelpers IdlJitterSvcBaseAdapter IdlJitterSvcNatBoolOperations IdlJitterSvcIntervalOperations IdlJitterSvcScheduleOperations IdlJitterSvcJobOperations IdlPreemptionParameterCorrespondence IdlTaskPreemptionParametersCorrespondence IdlIdealAbstractRtaHelpers IdlArrivalSequenceBaseAdapter IdlArrivalSequenceOperations IdlTaskScheduleCorrespondence IdlCurvesCorrespondence IdlRequestBoundFunctionCorrespondence IdlSequentialityCorrespondence IdlServiceOfJobsCorrespondence IdlSupplyScheduleBaseAdapter IdlSupplyScheduleFiniteOperations IdlSupplyScheduleOperations IdlSupplyBaseAdapter IdlSupplyNatBoolOperations IdlSupplyIntervalOperations IdlSupplyCorrespondence IdlIbfTaskHelpers IdlIbfSupplyTaskCorrespondence IdlIbfTaskFullHelpers IdlServiceInversionPredCorrespondence IdlInterferenceCorrespondence IdlPriorityInversionCorrespondence IdlPreemptionTimeCorrespondence IdlEdfAthepBoundCorrespondence IdlStateRel RtaIdealEdfBoundedNpsCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN is_in_search_space_correspondence". exact Logic.I. Qed.
Print Assumptions is_in_search_space_correspondence.
Goal Logic.True. idtac "AUDIT_END is_in_search_space_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN blocking_bound_decreasing_correspondence". exact Logic.I. Qed.
Print Assumptions blocking_bound_decreasing_correspondence.
Goal Logic.True. idtac "AUDIT_END blocking_bound_decreasing_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN task_with_equal_deadline_exists_correspondence". exact Logic.I. Qed.
Print Assumptions task_with_equal_deadline_exists_correspondence.
Goal Logic.True. idtac "AUDIT_END task_with_equal_deadline_exists_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN search_space_inclusion_correspondence". exact Logic.I. Qed.
Print Assumptions search_space_inclusion_correspondence.
Goal Logic.True. idtac "AUDIT_END search_space_inclusion_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments_correspondence". exact Logic.I. Qed.
Print Assumptions uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments_correspondence.
Goal Logic.True. idtac "AUDIT_END uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rien_all_jobs_from_taskset_rel". exact Logic.I. Qed.
Print Assumptions rien_all_jobs_from_taskset_rel.
Goal Logic.True. idtac "AUDIT_END rien_all_jobs_from_taskset_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rien_valid_taskset_curve_rel". exact Logic.I. Qed.
Print Assumptions rien_valid_taskset_curve_rel.
Goal Logic.True. idtac "AUDIT_END rien_valid_taskset_curve_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rien_task_deadline_of_job_related". exact Logic.I. Qed.
Print Assumptions rien_task_deadline_of_job_related.
Goal Logic.True. idtac "AUDIT_END rien_task_deadline_of_job_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rien_edf_rel". exact Logic.I. Qed.
Print Assumptions rien_edf_rel.
Goal Logic.True. idtac "AUDIT_END rien_edf_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rien_basic_ready_at". exact Logic.I. Qed.
Print Assumptions rien_basic_ready_at.
Goal Logic.True. idtac "AUDIT_END rien_basic_ready_at". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rien_backlogged_rel". exact Logic.I. Qed.
Print Assumptions rien_backlogged_rel.
Goal Logic.True. idtac "AUDIT_END rien_backlogged_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rien_respects_jlfp_rel". exact Logic.I. Qed.
Print Assumptions rien_respects_jlfp_rel.
Goal Logic.True. idtac "AUDIT_END rien_respects_jlfp_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rien_decide_not". exact Logic.I. Qed.
Print Assumptions rien_decide_not.
Goal Logic.True. idtac "AUDIT_END rien_decide_not". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rien_nat_neqb_related". exact Logic.I. Qed.
Print Assumptions rien_nat_neqb_related.
Goal Logic.True. idtac "AUDIT_END rien_nat_neqb_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rien_has_canonical". exact Logic.I. Qed.
Print Assumptions rien_has_canonical.
Goal Logic.True. idtac "AUDIT_END rien_has_canonical". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rien_has_related". exact Logic.I. Qed.
Print Assumptions rien_has_related.
Goal Logic.True. idtac "AUDIT_END rien_has_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rien_bpi_task_rbf_changes_rel". exact Logic.I. Qed.
Print Assumptions rien_bpi_task_rbf_changes_rel.
Goal Logic.True. idtac "AUDIT_END rien_bpi_task_rbf_changes_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rien_bpi_bound_changes_rel". exact Logic.I. Qed.
Print Assumptions rien_bpi_bound_changes_rel.
Goal Logic.True. idtac "AUDIT_END rien_bpi_bound_changes_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rien_bpi_pi_changes_rel". exact Logic.I. Qed.
Print Assumptions rien_bpi_pi_changes_rel.
Goal Logic.True. idtac "AUDIT_END rien_bpi_pi_changes_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rien_bpi_is_in_search_space_rel". exact Logic.I. Qed.
Print Assumptions rien_bpi_is_in_search_space_rel.
Goal Logic.True. idtac "AUDIT_END rien_bpi_is_in_search_space_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rien_forall_jp". exact Logic.I. Qed.
Print Assumptions rien_forall_jp.
Goal Logic.True. idtac "AUDIT_END rien_forall_jp". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rien_bigmax_canonical". exact Logic.I. Qed.
Print Assumptions rien_bigmax_canonical.
Goal Logic.True. idtac "AUDIT_END rien_bigmax_canonical". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rien_bigmax_related". exact Logic.I. Qed.
Print Assumptions rien_bigmax_related.
Goal Logic.True. idtac "AUDIT_END rien_bigmax_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rien_blocking_relevant_rel". exact Logic.I. Qed.
Print Assumptions rien_blocking_relevant_rel.
Goal Logic.True. idtac "AUDIT_END rien_blocking_relevant_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rien_blocking_bound_rel". exact Logic.I. Qed.
Print Assumptions rien_blocking_bound_rel.
Goal Logic.True. idtac "AUDIT_END rien_blocking_bound_rel". exact Logic.I. Qed.
