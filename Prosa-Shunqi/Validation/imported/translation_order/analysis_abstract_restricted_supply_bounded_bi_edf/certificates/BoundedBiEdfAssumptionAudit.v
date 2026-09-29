From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence WorkloadCorrespondence AbstractDefinitionsBaseAdapter ServiceBaseAdapter ServiceNatBoolOperations AbstractDefinitionsArrivalOperations AbstractDefinitionsClasses AbstractDefinitionsNatBoolOperations AbstractDefinitionsIntervalOperations AbstractDefinitionsOperations AbstractDefinitionsSums AbstractDefinitionsLogical ServiceIntervalOperations ServiceScheduleOperations AbstractDefinitionsPendingOperations AbstractDefinitionsTaskOperations AbstractDefinitionsBusyIntervalHelpers AbstractRtaHelpers JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence TaskPreemptionParametersCorrespondence IdealAbstractRtaHelpers ArrivalSequenceBaseAdapter ArrivalSequenceOperations TaskScheduleCorrespondence CurvesCorrespondence RequestBoundFunctionCorrespondence SequentialityCorrespondence ServiceOfJobsCorrespondence SupplyScheduleBaseAdapter SupplyScheduleFiniteOperations SupplyScheduleOperations SupplyBaseAdapter SupplyNatBoolOperations SupplyIntervalOperations SupplyCorrespondence IbfTaskHelpers IbfSupplyTaskCorrespondence IbfTaskFullHelpers ServiceInversionPredCorrespondence InterferenceCorrespondence RsIwHelpers WorkloadBoundedCorrespondence ServiceInversionBusyPrefixCorrespondence ArrivalSequenceCorrespondence BusyIntervalClassicalHelpers PredHelpers SbfBusyCorrespondence PreemptionTimeCorrespondence PriorityDrivenCorrespondence PcoBaseAdapter EdfPiBoundCorrespondence BoundedBiEdfCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN longest_bi_with_pi_bound_is_valid_correspondence". exact Logic.I. Qed.
Print Assumptions longest_bi_with_pi_bound_is_valid_correspondence.
Goal Logic.True. idtac "AUDIT_END longest_bi_with_pi_bound_is_valid_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN busy_intervals_are_bounded_rs_edf_correspondence". exact Logic.I. Qed.
Print Assumptions busy_intervals_are_bounded_rs_edf_correspondence.
Goal Logic.True. idtac "AUDIT_END busy_intervals_are_bounded_rs_edf_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbd_fun1_to_target_rel". exact Logic.I. Qed.
Print Assumptions bbd_fun1_to_target_rel.
Goal Logic.True. idtac "AUDIT_END bbd_fun1_to_target_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbd_fun1_to_source_rel". exact Logic.I. Qed.
Print Assumptions bbd_fun1_to_source_rel.
Goal Logic.True. idtac "AUDIT_END bbd_fun1_to_source_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbd_forall_fun1". exact Logic.I. Qed.
Print Assumptions bbd_forall_fun1.
Goal Logic.True. idtac "AUDIT_END bbd_forall_fun1". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbd_forall_sbf". exact Logic.I. Qed.
Print Assumptions bbd_forall_sbf.
Goal Logic.True. idtac "AUDIT_END bbd_forall_sbf". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbd_task_cost_of_job_related". exact Logic.I. Qed.
Print Assumptions bbd_task_cost_of_job_related.
Goal Logic.True. idtac "AUDIT_END bbd_task_cost_of_job_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbd_valid_job_costs_rel". exact Logic.I. Qed.
Print Assumptions bbd_valid_job_costs_rel.
Goal Logic.True. idtac "AUDIT_END bbd_valid_job_costs_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbd_all_jobs_from_taskset_rel". exact Logic.I. Qed.
Print Assumptions bbd_all_jobs_from_taskset_rel.
Goal Logic.True. idtac "AUDIT_END bbd_all_jobs_from_taskset_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbd_forall_ma". exact Logic.I. Qed.
Print Assumptions bbd_forall_ma.
Goal Logic.True. idtac "AUDIT_END bbd_forall_ma". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbd_forall_jp". exact Logic.I. Qed.
Print Assumptions bbd_forall_jp.
Goal Logic.True. idtac "AUDIT_END bbd_forall_jp". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbd_forall_tms". exact Logic.I. Qed.
Print Assumptions bbd_forall_tms.
Goal Logic.True. idtac "AUDIT_END bbd_forall_tms". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbd_respects_jlfp_rel". exact Logic.I. Qed.
Print Assumptions bbd_respects_jlfp_rel.
Goal Logic.True. idtac "AUDIT_END bbd_respects_jlfp_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbd_task_deadline_of_job_related". exact Logic.I. Qed.
Print Assumptions bbd_task_deadline_of_job_related.
Goal Logic.True. idtac "AUDIT_END bbd_task_deadline_of_job_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbd_edf_rel". exact Logic.I. Qed.
Print Assumptions bbd_edf_rel.
Goal Logic.True. idtac "AUDIT_END bbd_edf_rel". exact Logic.I. Qed.
