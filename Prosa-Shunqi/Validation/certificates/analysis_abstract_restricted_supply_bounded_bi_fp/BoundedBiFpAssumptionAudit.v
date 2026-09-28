From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence WorkloadCorrespondence AbstractDefinitionsBaseAdapter ServiceBaseAdapter ServiceNatBoolOperations AbstractDefinitionsArrivalOperations AbstractDefinitionsClasses AbstractDefinitionsNatBoolOperations AbstractDefinitionsIntervalOperations AbstractDefinitionsOperations AbstractDefinitionsSums AbstractDefinitionsLogical ServiceIntervalOperations ServiceScheduleOperations AbstractDefinitionsPendingOperations AbstractDefinitionsTaskOperations AbstractDefinitionsBusyIntervalHelpers AbstractRtaHelpers JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence TaskPreemptionParametersCorrespondence IdealAbstractRtaHelpers ArrivalSequenceBaseAdapter ArrivalSequenceOperations TaskScheduleCorrespondence CurvesCorrespondence RequestBoundFunctionCorrespondence SequentialityCorrespondence ServiceOfJobsCorrespondence SupplyScheduleBaseAdapter SupplyScheduleFiniteOperations SupplyScheduleOperations SupplyBaseAdapter SupplyNatBoolOperations SupplyIntervalOperations SupplyCorrespondence IbfTaskHelpers IbfSupplyTaskCorrespondence IbfTaskFullHelpers ServiceInversionPredCorrespondence InterferenceCorrespondence RsIwHelpers WorkloadBoundedCorrespondence ServiceInversionBusyPrefixCorrespondence ArrivalSequenceCorrespondence BusyIntervalClassicalHelpers PredHelpers SbfBusyCorrespondence PreemptionTimeCorrespondence PriorityDrivenCorrespondence PcoBaseAdapter BlockingBoundFpCorrespondence BoundedBiFpCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN busy_intervals_are_bounded_rs_fp_correspondence". exact Logic.I. Qed.
Print Assumptions busy_intervals_are_bounded_rs_fp_correspondence.
Goal Logic.True. idtac "AUDIT_END busy_intervals_are_bounded_rs_fp_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbf_transport". exact Logic.I. Qed.
Print Assumptions bbf_transport.
Goal Logic.True. idtac "AUDIT_END bbf_transport". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbf_forall_fp". exact Logic.I. Qed.
Print Assumptions bbf_forall_fp.
Goal Logic.True. idtac "AUDIT_END bbf_forall_fp". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbf_reflexive_task_priorities_rel". exact Logic.I. Qed.
Print Assumptions bbf_reflexive_task_priorities_rel.
Goal Logic.True. idtac "AUDIT_END bbf_reflexive_task_priorities_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbf_transitive_task_priorities_rel". exact Logic.I. Qed.
Print Assumptions bbf_transitive_task_priorities_rel.
Goal Logic.True. idtac "AUDIT_END bbf_transitive_task_priorities_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbf_fp_to_jlfp_rel". exact Logic.I. Qed.
Print Assumptions bbf_fp_to_jlfp_rel.
Goal Logic.True. idtac "AUDIT_END bbf_fp_to_jlfp_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbf_fun1_to_target_rel". exact Logic.I. Qed.
Print Assumptions bbf_fun1_to_target_rel.
Goal Logic.True. idtac "AUDIT_END bbf_fun1_to_target_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbf_fun1_to_source_rel". exact Logic.I. Qed.
Print Assumptions bbf_fun1_to_source_rel.
Goal Logic.True. idtac "AUDIT_END bbf_fun1_to_source_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbf_forall_fun1". exact Logic.I. Qed.
Print Assumptions bbf_forall_fun1.
Goal Logic.True. idtac "AUDIT_END bbf_forall_fun1". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbf_forall_sbf". exact Logic.I. Qed.
Print Assumptions bbf_forall_sbf.
Goal Logic.True. idtac "AUDIT_END bbf_forall_sbf". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbf_task_cost_of_job_related". exact Logic.I. Qed.
Print Assumptions bbf_task_cost_of_job_related.
Goal Logic.True. idtac "AUDIT_END bbf_task_cost_of_job_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbf_valid_job_costs_rel". exact Logic.I. Qed.
Print Assumptions bbf_valid_job_costs_rel.
Goal Logic.True. idtac "AUDIT_END bbf_valid_job_costs_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbf_all_jobs_from_taskset_rel". exact Logic.I. Qed.
Print Assumptions bbf_all_jobs_from_taskset_rel.
Goal Logic.True. idtac "AUDIT_END bbf_all_jobs_from_taskset_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbf_forall_ma". exact Logic.I. Qed.
Print Assumptions bbf_forall_ma.
Goal Logic.True. idtac "AUDIT_END bbf_forall_ma". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbf_forall_jp". exact Logic.I. Qed.
Print Assumptions bbf_forall_jp.
Goal Logic.True. idtac "AUDIT_END bbf_forall_jp". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbf_forall_tms". exact Logic.I. Qed.
Print Assumptions bbf_forall_tms.
Goal Logic.True. idtac "AUDIT_END bbf_forall_tms". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbf_respects_fp_rel". exact Logic.I. Qed.
Print Assumptions bbf_respects_fp_rel.
Goal Logic.True. idtac "AUDIT_END bbf_respects_fp_rel". exact Logic.I. Qed.
