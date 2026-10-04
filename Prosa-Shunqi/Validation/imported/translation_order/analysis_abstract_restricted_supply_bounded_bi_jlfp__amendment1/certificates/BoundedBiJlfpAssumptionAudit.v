From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence WorkloadCorrespondence AbstractDefinitionsBaseAdapter ServiceBaseAdapter ServiceNatBoolOperations AbstractDefinitionsArrivalOperations AbstractDefinitionsClasses AbstractDefinitionsNatBoolOperations AbstractDefinitionsIntervalOperations AbstractDefinitionsOperations AbstractDefinitionsSums AbstractDefinitionsLogical ServiceIntervalOperations ServiceScheduleOperations AbstractDefinitionsPendingOperations AbstractDefinitionsTaskOperations AbstractDefinitionsBusyIntervalHelpers AbstractRtaHelpers JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence TaskPreemptionParametersCorrespondence IdealAbstractRtaHelpers ArrivalSequenceBaseAdapter ArrivalSequenceOperations TaskScheduleCorrespondence CurvesCorrespondence RequestBoundFunctionCorrespondence SequentialityCorrespondence ServiceOfJobsCorrespondence SupplyScheduleBaseAdapter SupplyScheduleFiniteOperations SupplyScheduleOperations SupplyBaseAdapter SupplyNatBoolOperations SupplyIntervalOperations SupplyCorrespondence IbfTaskHelpers IbfSupplyTaskCorrespondence IbfTaskFullHelpers ServiceInversionPredCorrespondence InterferenceCorrespondence RsIwHelpers WorkloadBoundedCorrespondence ServiceInversionBusyPrefixCorrespondence ArrivalSequenceCorrespondence BusyIntervalClassicalHelpers PredHelpers SbfBusyCorrespondence BoundedBiJlfpCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN job_arrival_is_bounded_correspondence". exact Logic.I. Qed.
Print Assumptions job_arrival_is_bounded_correspondence.
Goal Logic.True. idtac "AUDIT_END job_arrival_is_bounded_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN busy_intervals_are_bounded_rs_jlfp_correspondence". exact Logic.I. Qed.
Print Assumptions busy_intervals_are_bounded_rs_jlfp_correspondence.
Goal Logic.True. idtac "AUDIT_END busy_intervals_are_bounded_rs_jlfp_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbj_fun1_to_target_rel". exact Logic.I. Qed.
Print Assumptions bbj_fun1_to_target_rel.
Goal Logic.True. idtac "AUDIT_END bbj_fun1_to_target_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbj_fun1_to_source_rel". exact Logic.I. Qed.
Print Assumptions bbj_fun1_to_source_rel.
Goal Logic.True. idtac "AUDIT_END bbj_fun1_to_source_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbj_forall_fun1". exact Logic.I. Qed.
Print Assumptions bbj_forall_fun1.
Goal Logic.True. idtac "AUDIT_END bbj_forall_fun1". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbj_forall_sbf". exact Logic.I. Qed.
Print Assumptions bbj_forall_sbf.
Goal Logic.True. idtac "AUDIT_END bbj_forall_sbf". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbj_task_cost_of_job_related". exact Logic.I. Qed.
Print Assumptions bbj_task_cost_of_job_related.
Goal Logic.True. idtac "AUDIT_END bbj_task_cost_of_job_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbj_valid_job_costs_rel". exact Logic.I. Qed.
Print Assumptions bbj_valid_job_costs_rel.
Goal Logic.True. idtac "AUDIT_END bbj_valid_job_costs_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbj_all_jobs_from_taskset_rel". exact Logic.I. Qed.
Print Assumptions bbj_all_jobs_from_taskset_rel.
Goal Logic.True. idtac "AUDIT_END bbj_all_jobs_from_taskset_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbj_forall_ma". exact Logic.I. Qed.
Print Assumptions bbj_forall_ma.
Goal Logic.True. idtac "AUDIT_END bbj_forall_ma". exact Logic.I. Qed.
