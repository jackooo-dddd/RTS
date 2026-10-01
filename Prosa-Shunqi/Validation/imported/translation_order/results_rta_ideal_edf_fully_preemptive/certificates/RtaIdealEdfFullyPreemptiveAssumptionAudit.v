From FoundationCertificates Require Import
  IdlArrivalsSeqBaseAdapter IdlArrivalsSeqOperations IdlArrivalsSeqCorrespondence IdlArrivalsCorrespondence IdlWorkloadCorrespondence IdlAbstractDefinitionsBaseAdapter IdlServiceBaseAdapter IdlServiceNatBoolOperations IdlAbstractDefinitionsArrivalOperations IdlAbstractDefinitionsClasses IdlAbstractDefinitionsNatBoolOperations IdlAbstractDefinitionsIntervalOperations IdlAbstractDefinitionsOperations IdlAbstractDefinitionsSums IdlAbstractDefinitionsLogical IdlServiceIntervalOperations IdlServiceScheduleOperations IdlAbstractDefinitionsPendingOperations IdlAbstractDefinitionsTaskOperations IdlAbstractDefinitionsBusyIntervalHelpers IdlAbstractRtaHelpers IdlJitterSvcBaseAdapter IdlJitterSvcNatBoolOperations IdlJitterSvcIntervalOperations IdlJitterSvcScheduleOperations IdlJitterSvcJobOperations IdlPreemptionParameterCorrespondence IdlTaskPreemptionParametersCorrespondence IdlIdealAbstractRtaHelpers IdlArrivalSequenceBaseAdapter IdlArrivalSequenceOperations IdlTaskScheduleCorrespondence IdlCurvesCorrespondence IdlRequestBoundFunctionCorrespondence IdlSequentialityCorrespondence IdlServiceOfJobsCorrespondence IdlSupplyScheduleBaseAdapter IdlSupplyScheduleFiniteOperations IdlSupplyScheduleOperations IdlSupplyBaseAdapter IdlSupplyNatBoolOperations IdlSupplyIntervalOperations IdlSupplyCorrespondence IdlIbfTaskHelpers IdlIbfSupplyTaskCorrespondence IdlIbfTaskFullHelpers IdlServiceInversionPredCorrespondence IdlInterferenceCorrespondence IdlPriorityInversionCorrespondence IdlPreemptionTimeCorrespondence IdlEdfAthepBoundCorrespondence IdlStateRel RtaIdealEdfFullyPreemptiveCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN uniprocessor_response_time_bound_fully_preemptive_edf_correspondence". exact Logic.I. Qed.
Print Assumptions uniprocessor_response_time_bound_fully_preemptive_edf_correspondence.
Goal Logic.True. idtac "AUDIT_END uniprocessor_response_time_bound_fully_preemptive_edf_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN riex_all_jobs_from_taskset_rel". exact Logic.I. Qed.
Print Assumptions riex_all_jobs_from_taskset_rel.
Goal Logic.True. idtac "AUDIT_END riex_all_jobs_from_taskset_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN riex_valid_taskset_curve_rel". exact Logic.I. Qed.
Print Assumptions riex_valid_taskset_curve_rel.
Goal Logic.True. idtac "AUDIT_END riex_valid_taskset_curve_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN riex_task_deadline_of_job_related". exact Logic.I. Qed.
Print Assumptions riex_task_deadline_of_job_related.
Goal Logic.True. idtac "AUDIT_END riex_task_deadline_of_job_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN riex_edf_rel". exact Logic.I. Qed.
Print Assumptions riex_edf_rel.
Goal Logic.True. idtac "AUDIT_END riex_edf_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN riex_basic_ready_at". exact Logic.I. Qed.
Print Assumptions riex_basic_ready_at.
Goal Logic.True. idtac "AUDIT_END riex_basic_ready_at". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN riex_backlogged_rel". exact Logic.I. Qed.
Print Assumptions riex_backlogged_rel.
Goal Logic.True. idtac "AUDIT_END riex_backlogged_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN riex_respects_jlfp_rel". exact Logic.I. Qed.
Print Assumptions riex_respects_jlfp_rel.
Goal Logic.True. idtac "AUDIT_END riex_respects_jlfp_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN riex_decide_not". exact Logic.I. Qed.
Print Assumptions riex_decide_not.
Goal Logic.True. idtac "AUDIT_END riex_decide_not". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN riex_nat_neqb_related". exact Logic.I. Qed.
Print Assumptions riex_nat_neqb_related.
Goal Logic.True. idtac "AUDIT_END riex_nat_neqb_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN riex_has_canonical". exact Logic.I. Qed.
Print Assumptions riex_has_canonical.
Goal Logic.True. idtac "AUDIT_END riex_has_canonical". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN riex_has_related". exact Logic.I. Qed.
Print Assumptions riex_has_related.
Goal Logic.True. idtac "AUDIT_END riex_has_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN riex_bpi_task_rbf_changes_rel". exact Logic.I. Qed.
Print Assumptions riex_bpi_task_rbf_changes_rel.
Goal Logic.True. idtac "AUDIT_END riex_bpi_task_rbf_changes_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN riex_bpi_bound_changes_rel". exact Logic.I. Qed.
Print Assumptions riex_bpi_bound_changes_rel.
Goal Logic.True. idtac "AUDIT_END riex_bpi_bound_changes_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN riex_bnps_is_in_search_space_rel". exact Logic.I. Qed.
Print Assumptions riex_bnps_is_in_search_space_rel.
Goal Logic.True. idtac "AUDIT_END riex_bnps_is_in_search_space_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN riex_fully_preemptive_job_related". exact Logic.I. Qed.
Print Assumptions riex_fully_preemptive_job_related.
Goal Logic.True. idtac "AUDIT_END riex_fully_preemptive_job_related". exact Logic.I. Qed.
