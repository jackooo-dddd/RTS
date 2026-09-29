From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence WorkloadCorrespondence AbstractDefinitionsBaseAdapter ServiceBaseAdapter ServiceNatBoolOperations AbstractDefinitionsArrivalOperations AbstractDefinitionsClasses AbstractDefinitionsNatBoolOperations AbstractDefinitionsIntervalOperations AbstractDefinitionsOperations AbstractDefinitionsSums AbstractDefinitionsLogical ServiceIntervalOperations ServiceScheduleOperations AbstractDefinitionsPendingOperations AbstractDefinitionsTaskOperations AbstractDefinitionsBusyIntervalHelpers AbstractRtaHelpers JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence TaskPreemptionParametersCorrespondence IdealAbstractRtaHelpers ArrivalSequenceBaseAdapter ArrivalSequenceOperations TaskScheduleCorrespondence CurvesCorrespondence RequestBoundFunctionCorrespondence SequentialityCorrespondence ServiceOfJobsCorrespondence SupplyScheduleBaseAdapter SupplyScheduleFiniteOperations SupplyScheduleOperations SupplyBaseAdapter SupplyNatBoolOperations SupplyIntervalOperations SupplyCorrespondence IbfTaskHelpers IbfSupplyTaskCorrespondence IbfTaskFullHelpers ServiceInversionPredCorrespondence InterferenceCorrespondence RsIwHelpers WorkloadBoundedCorrespondence ServiceInversionBusyPrefixCorrespondence ArrivalSequenceCorrespondence BusyIntervalClassicalHelpers PredHelpers SbfBusyCorrespondence PreemptionTimeCorrespondence PriorityDrivenCorrespondence PcoBaseAdapter PcoStaticOrder PcoDynamicOrder PriorityCoercionCorrespondence BlockingBoundFpCorrespondence NatSubCorrespondence PriorityGelHelpers PriorityElfHelpers BlockingBoundElfCorrespondence BoundedBiElfCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN busy_intervals_are_bounded_rs_elf_correspondence". exact Logic.I. Qed.
Print Assumptions busy_intervals_are_bounded_rs_elf_correspondence.
Goal Logic.True. idtac "AUDIT_END busy_intervals_are_bounded_rs_elf_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbe_fun1_to_target_rel". exact Logic.I. Qed.
Print Assumptions bbe_fun1_to_target_rel.
Goal Logic.True. idtac "AUDIT_END bbe_fun1_to_target_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbe_fun1_to_source_rel". exact Logic.I. Qed.
Print Assumptions bbe_fun1_to_source_rel.
Goal Logic.True. idtac "AUDIT_END bbe_fun1_to_source_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbe_forall_fun1". exact Logic.I. Qed.
Print Assumptions bbe_forall_fun1.
Goal Logic.True. idtac "AUDIT_END bbe_forall_fun1". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbe_forall_sbf". exact Logic.I. Qed.
Print Assumptions bbe_forall_sbf.
Goal Logic.True. idtac "AUDIT_END bbe_forall_sbf". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbe_task_cost_of_job_related". exact Logic.I. Qed.
Print Assumptions bbe_task_cost_of_job_related.
Goal Logic.True. idtac "AUDIT_END bbe_task_cost_of_job_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbe_valid_job_costs_rel". exact Logic.I. Qed.
Print Assumptions bbe_valid_job_costs_rel.
Goal Logic.True. idtac "AUDIT_END bbe_valid_job_costs_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbe_all_jobs_from_taskset_rel". exact Logic.I. Qed.
Print Assumptions bbe_all_jobs_from_taskset_rel.
Goal Logic.True. idtac "AUDIT_END bbe_all_jobs_from_taskset_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbe_forall_ma". exact Logic.I. Qed.
Print Assumptions bbe_forall_ma.
Goal Logic.True. idtac "AUDIT_END bbe_forall_ma". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbe_forall_jp". exact Logic.I. Qed.
Print Assumptions bbe_forall_jp.
Goal Logic.True. idtac "AUDIT_END bbe_forall_jp". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbe_forall_tms". exact Logic.I. Qed.
Print Assumptions bbe_forall_tms.
Goal Logic.True. idtac "AUDIT_END bbe_forall_tms". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbe_respects_jlfp_rel". exact Logic.I. Qed.
Print Assumptions bbe_respects_jlfp_rel.
Goal Logic.True. idtac "AUDIT_END bbe_respects_jlfp_rel". exact Logic.I. Qed.
