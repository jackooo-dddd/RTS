From FoundationCertificates Require Import
  IdlArrivalsSeqBaseAdapter IdlArrivalsSeqOperations IdlArrivalsSeqCorrespondence IdlArrivalsCorrespondence IdlWorkloadCorrespondence IdlAbstractDefinitionsBaseAdapter IdlServiceBaseAdapter IdlServiceNatBoolOperations IdlAbstractDefinitionsArrivalOperations IdlAbstractDefinitionsClasses IdlAbstractDefinitionsNatBoolOperations IdlAbstractDefinitionsIntervalOperations IdlAbstractDefinitionsOperations IdlAbstractDefinitionsSums IdlAbstractDefinitionsLogical IdlServiceIntervalOperations IdlServiceScheduleOperations IdlAbstractDefinitionsPendingOperations IdlAbstractDefinitionsTaskOperations IdlAbstractDefinitionsBusyIntervalHelpers IdlAbstractRtaHelpers IdlJitterSvcBaseAdapter IdlJitterSvcNatBoolOperations IdlJitterSvcIntervalOperations IdlJitterSvcScheduleOperations IdlJitterSvcJobOperations IdlPreemptionParameterCorrespondence IdlTaskPreemptionParametersCorrespondence IdlIdealAbstractRtaHelpers IdlArrivalSequenceBaseAdapter IdlArrivalSequenceOperations IdlTaskScheduleCorrespondence IdlCurvesCorrespondence IdlRequestBoundFunctionCorrespondence IdlSequentialityCorrespondence IdlServiceOfJobsCorrespondence IdlSupplyScheduleBaseAdapter IdlSupplyScheduleFiniteOperations IdlSupplyScheduleOperations IdlSupplyBaseAdapter IdlSupplyNatBoolOperations IdlSupplyIntervalOperations IdlSupplyCorrespondence IdlIbfTaskHelpers IdlIbfSupplyTaskCorrespondence IdlIbfTaskFullHelpers IdlServiceInversionPredCorrespondence IdlInterferenceCorrespondence IdlPriorityInversionCorrespondence IdlPreemptionTimeCorrespondence IdlNatSubCorrespondence IdlFixpointBaseCorrespondence IdlFixpointMonotoneCorrespondence IdlFixpointMaxOperations IdlStateRel RtaIdealFpCompFullyPreemptiveCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN uniprocessor_response_time_bound_fully_preemptive_fp_correspondence". exact Logic.I. Qed.
Print Assumptions uniprocessor_response_time_bound_fully_preemptive_fp_correspondence.
Goal Logic.True. idtac "AUDIT_END uniprocessor_response_time_bound_fully_preemptive_fp_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rifc_forall_fp". exact Logic.I. Qed.
Print Assumptions rifc_forall_fp.
Goal Logic.True. idtac "AUDIT_END rifc_forall_fp". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rifc_reflexive_task_priorities_rel". exact Logic.I. Qed.
Print Assumptions rifc_reflexive_task_priorities_rel.
Goal Logic.True. idtac "AUDIT_END rifc_reflexive_task_priorities_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rifc_fp_to_jlfp_rel". exact Logic.I. Qed.
Print Assumptions rifc_fp_to_jlfp_rel.
Goal Logic.True. idtac "AUDIT_END rifc_fp_to_jlfp_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rifc_all_jobs_from_taskset_rel". exact Logic.I. Qed.
Print Assumptions rifc_all_jobs_from_taskset_rel.
Goal Logic.True. idtac "AUDIT_END rifc_all_jobs_from_taskset_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rifc_valid_taskset_curve_rel". exact Logic.I. Qed.
Print Assumptions rifc_valid_taskset_curve_rel.
Goal Logic.True. idtac "AUDIT_END rifc_valid_taskset_curve_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rifc_transitive_task_priorities_rel". exact Logic.I. Qed.
Print Assumptions rifc_transitive_task_priorities_rel.
Goal Logic.True. idtac "AUDIT_END rifc_transitive_task_priorities_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rifc_backlogged_rel". exact Logic.I. Qed.
Print Assumptions rifc_backlogged_rel.
Goal Logic.True. idtac "AUDIT_END rifc_backlogged_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rifc_respects_fp_rel". exact Logic.I. Qed.
Print Assumptions rifc_respects_fp_rel.
Goal Logic.True. idtac "AUDIT_END rifc_respects_fp_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rifc_decide_not". exact Logic.I. Qed.
Print Assumptions rifc_decide_not.
Goal Logic.True. idtac "AUDIT_END rifc_decide_not". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rifc_nat_neqb_related". exact Logic.I. Qed.
Print Assumptions rifc_nat_neqb_related.
Goal Logic.True. idtac "AUDIT_END rifc_nat_neqb_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rifc_bpi_is_in_search_space_rel". exact Logic.I. Qed.
Print Assumptions rifc_bpi_is_in_search_space_rel.
Goal Logic.True. idtac "AUDIT_END rifc_bpi_is_in_search_space_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rifc_sequential_ready_at". exact Logic.I. Qed.
Print Assumptions rifc_sequential_ready_at.
Goal Logic.True. idtac "AUDIT_END rifc_sequential_ready_at". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rifc_fully_preemptive_job_related". exact Logic.I. Qed.
Print Assumptions rifc_fully_preemptive_job_related.
Goal Logic.True. idtac "AUDIT_END rifc_fully_preemptive_job_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rifc_eq_sym_rel". exact Logic.I. Qed.
Print Assumptions rifc_eq_sym_rel.
Goal Logic.True. idtac "AUDIT_END rifc_eq_sym_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rifc_bool_rel". exact Logic.I. Qed.
Print Assumptions rifc_bool_rel.
Goal Logic.True. idtac "AUDIT_END rifc_bool_rel". exact Logic.I. Qed.
