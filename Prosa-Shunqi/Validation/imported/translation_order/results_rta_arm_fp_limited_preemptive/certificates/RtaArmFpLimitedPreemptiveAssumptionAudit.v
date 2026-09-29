From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence WorkloadCorrespondence AbstractDefinitionsBaseAdapter ServiceBaseAdapter ServiceNatBoolOperations AbstractDefinitionsArrivalOperations AbstractDefinitionsClasses AbstractDefinitionsNatBoolOperations AbstractDefinitionsIntervalOperations AbstractDefinitionsOperations AbstractDefinitionsSums AbstractDefinitionsLogical ServiceIntervalOperations ServiceScheduleOperations AbstractDefinitionsPendingOperations AbstractDefinitionsTaskOperations AbstractDefinitionsBusyIntervalHelpers AbstractRtaHelpers JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence TaskPreemptionParametersCorrespondence IdealAbstractRtaHelpers ArrivalSequenceBaseAdapter ArrivalSequenceOperations TaskScheduleCorrespondence CurvesCorrespondence RequestBoundFunctionCorrespondence SequentialityCorrespondence ServiceOfJobsCorrespondence SupplyScheduleBaseAdapter SupplyScheduleFiniteOperations SupplyScheduleOperations SupplyBaseAdapter SupplyNatBoolOperations SupplyIntervalOperations SupplyCorrespondence IbfTaskHelpers IbfSupplyTaskCorrespondence IbfTaskFullHelpers ServiceInversionPredCorrespondence InterferenceCorrespondence RsIwHelpers WorkloadBoundedCorrespondence ServiceInversionBusyPrefixCorrespondence ArrivalSequenceCorrespondence BusyIntervalClassicalHelpers PredHelpers SbfBusyCorrespondence PreemptionTimeCorrespondence PriorityDrivenCorrespondence PcoBaseAdapter BlockingBoundFpCorrespondence BoundedBiFpCorrespondence SearchSpaceFpCorrespondence LimitedPreemptiveCorrespondence ScheduleLimitedPreemptiveCorrespondence TaskLimitedPreemptiveCorrespondence PredCorrespondence PlainCorrespondence NatSubCorrespondence DivModCorrespondence AverageCorrespondence RsPStateCover RtaArmFpLimitedPreemptiveCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN busy_window_recurrence_solution_correspondence". exact Logic.I. Qed.
Print Assumptions busy_window_recurrence_solution_correspondence.
Goal Logic.True. idtac "AUDIT_END busy_window_recurrence_solution_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rta_recurrence_solution_correspondence". exact Logic.I. Qed.
Print Assumptions rta_recurrence_solution_correspondence.
Goal Logic.True. idtac "AUDIT_END rta_recurrence_solution_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN uniprocessor_response_time_bound_limited_fp_correspondence". exact Logic.I. Qed.
Print Assumptions uniprocessor_response_time_bound_limited_fp_correspondence.
Goal Logic.True. idtac "AUDIT_END uniprocessor_response_time_bound_limited_fp_correspondence". exact Logic.I. Qed.

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

Goal Logic.True. idtac "AUDIT_BEGIN rlp_job_model_related". exact Logic.I. Qed.
Print Assumptions rlp_job_model_related.
Goal Logic.True. idtac "AUDIT_END rlp_job_model_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rfa_valid_task_arrival_sequence_rel". exact Logic.I. Qed.
Print Assumptions rfa_valid_task_arrival_sequence_rel.
Goal Logic.True. idtac "AUDIT_END rfa_valid_task_arrival_sequence_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rfa_basic_ready_at". exact Logic.I. Qed.
Print Assumptions rfa_basic_ready_at.
Goal Logic.True. idtac "AUDIT_END rfa_basic_ready_at". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rfp_respects_fp_rel". exact Logic.I. Qed.
Print Assumptions rfp_respects_fp_rel.
Goal Logic.True. idtac "AUDIT_END rfp_respects_fp_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rfa_sequential_tasks_rel". exact Logic.I. Qed.
Print Assumptions rfa_sequential_tasks_rel.
Goal Logic.True. idtac "AUDIT_END rfa_sequential_tasks_rel". exact Logic.I. Qed.
