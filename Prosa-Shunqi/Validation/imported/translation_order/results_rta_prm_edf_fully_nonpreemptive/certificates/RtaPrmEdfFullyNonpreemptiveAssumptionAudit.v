From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence WorkloadCorrespondence AbstractDefinitionsBaseAdapter ServiceBaseAdapter ServiceNatBoolOperations AbstractDefinitionsArrivalOperations AbstractDefinitionsClasses AbstractDefinitionsNatBoolOperations AbstractDefinitionsIntervalOperations AbstractDefinitionsOperations AbstractDefinitionsSums AbstractDefinitionsLogical ServiceIntervalOperations ServiceScheduleOperations AbstractDefinitionsPendingOperations AbstractDefinitionsTaskOperations AbstractDefinitionsBusyIntervalHelpers AbstractRtaHelpers JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence TaskPreemptionParametersCorrespondence IdealAbstractRtaHelpers ArrivalSequenceBaseAdapter ArrivalSequenceOperations TaskScheduleCorrespondence CurvesCorrespondence RequestBoundFunctionCorrespondence SequentialityCorrespondence ServiceOfJobsCorrespondence SupplyScheduleBaseAdapter SupplyScheduleFiniteOperations SupplyScheduleOperations SupplyBaseAdapter SupplyNatBoolOperations SupplyIntervalOperations SupplyCorrespondence IbfTaskHelpers IbfSupplyTaskCorrespondence IbfTaskFullHelpers ServiceInversionPredCorrespondence InterferenceCorrespondence RsIwHelpers WorkloadBoundedCorrespondence ServiceInversionBusyPrefixCorrespondence ArrivalSequenceCorrespondence BusyIntervalClassicalHelpers PredHelpers SbfBusyCorrespondence PreemptionTimeCorrespondence PriorityDrivenCorrespondence PcoBaseAdapter EdfAthepBoundCorrespondence BlockingBoundEdfCorrespondence SearchSpaceEdfCorrespondence EdfPiBoundCorrespondence PredCorrespondence PlainCorrespondence NatSubCorrespondence DivModCorrespondence PeriodicCorrespondence FsScheduleBaseAdapter FsScheduleFiniteOperations FsScheduleCorrespondence FsProcessorStateCorrespondence FactsSupplyPlatformPropertiesCorrespondence RsPStateCover RtaPrmEdfFullyNonpreemptiveCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN busy_window_recurrence_solution_correspondence". exact Logic.I. Qed.
Print Assumptions busy_window_recurrence_solution_correspondence.
Goal Logic.True. idtac "AUDIT_END busy_window_recurrence_solution_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rta_recurrence_solution_correspondence". exact Logic.I. Qed.
Print Assumptions rta_recurrence_solution_correspondence.
Goal Logic.True. idtac "AUDIT_END rta_recurrence_solution_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN uniprocessor_response_time_bound_fully_nonpreemptive_edf_correspondence". exact Logic.I. Qed.
Print Assumptions uniprocessor_response_time_bound_fully_nonpreemptive_edf_correspondence.
Goal Logic.True. idtac "AUDIT_END uniprocessor_response_time_bound_fully_nonpreemptive_edf_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rfp_fun1_to_target_rel". exact Logic.I. Qed.
Print Assumptions rfp_fun1_to_target_rel.
Goal Logic.True. idtac "AUDIT_END rfp_fun1_to_target_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rfp_fun1_to_source_rel". exact Logic.I. Qed.
Print Assumptions rfp_fun1_to_source_rel.
Goal Logic.True. idtac "AUDIT_END rfp_fun1_to_source_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rfp_forall_fun1". exact Logic.I. Qed.
Print Assumptions rfp_forall_fun1.
Goal Logic.True. idtac "AUDIT_END rfp_forall_fun1". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rfp_forall_sbf". exact Logic.I. Qed.
Print Assumptions rfp_forall_sbf.
Goal Logic.True. idtac "AUDIT_END rfp_forall_sbf". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rfp_task_cost_of_job_related". exact Logic.I. Qed.
Print Assumptions rfp_task_cost_of_job_related.
Goal Logic.True. idtac "AUDIT_END rfp_task_cost_of_job_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rfp_valid_job_costs_rel". exact Logic.I. Qed.
Print Assumptions rfp_valid_job_costs_rel.
Goal Logic.True. idtac "AUDIT_END rfp_valid_job_costs_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rfp_all_jobs_from_taskset_rel". exact Logic.I. Qed.
Print Assumptions rfp_all_jobs_from_taskset_rel.
Goal Logic.True. idtac "AUDIT_END rfp_all_jobs_from_taskset_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rfe_task_model_related". exact Logic.I. Qed.
Print Assumptions rfe_task_model_related.
Goal Logic.True. idtac "AUDIT_END rfe_task_model_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rfe_job_model_related". exact Logic.I. Qed.
Print Assumptions rfe_job_model_related.
Goal Logic.True. idtac "AUDIT_END rfe_job_model_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rfe_task_deadline_of_job_related". exact Logic.I. Qed.
Print Assumptions rfe_task_deadline_of_job_related.
Goal Logic.True. idtac "AUDIT_END rfe_task_deadline_of_job_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rfe_edf_rel". exact Logic.I. Qed.
Print Assumptions rfe_edf_rel.
Goal Logic.True. idtac "AUDIT_END rfe_edf_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rfa_valid_task_arrival_sequence_rel". exact Logic.I. Qed.
Print Assumptions rfa_valid_task_arrival_sequence_rel.
Goal Logic.True. idtac "AUDIT_END rfa_valid_task_arrival_sequence_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rfe_basic_ready_at". exact Logic.I. Qed.
Print Assumptions rfe_basic_ready_at.
Goal Logic.True. idtac "AUDIT_END rfe_basic_ready_at". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rfe_nonpreemptive_schedule_rel". exact Logic.I. Qed.
Print Assumptions rfe_nonpreemptive_schedule_rel.
Goal Logic.True. idtac "AUDIT_END rfe_nonpreemptive_schedule_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rfe_respects_jlfp_rel". exact Logic.I. Qed.
Print Assumptions rfe_respects_jlfp_rel.
Goal Logic.True. idtac "AUDIT_END rfe_respects_jlfp_rel". exact Logic.I. Qed.
