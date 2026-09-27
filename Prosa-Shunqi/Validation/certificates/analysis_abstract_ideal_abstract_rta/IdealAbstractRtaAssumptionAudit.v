From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence WorkloadCorrespondence AbstractDefinitionsBaseAdapter ServiceBaseAdapter ServiceNatBoolOperations AbstractDefinitionsArrivalOperations AbstractDefinitionsClasses AbstractDefinitionsNatBoolOperations AbstractDefinitionsIntervalOperations AbstractDefinitionsOperations AbstractDefinitionsSums AbstractDefinitionsLogical ServiceIntervalOperations ServiceScheduleOperations AbstractDefinitionsPendingOperations AbstractDefinitionsTaskOperations AbstractDefinitionsBusyIntervalHelpers AbstractRtaHelpers JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence TaskPreemptionParametersCorrespondence IdealAbstractRtaCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN nonpreemptive_interference_is_bounded_correspondence". exact Logic.I. Qed.
Print Assumptions nonpreemptive_interference_is_bounded_correspondence.
Goal Logic.True. idtac "AUDIT_END nonpreemptive_interference_is_bounded_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN uniprocessor_response_time_bound_ideal_correspondence". exact Logic.I. Qed.
Print Assumptions uniprocessor_response_time_bound_ideal_correspondence.
Goal Logic.True. idtac "AUDIT_END uniprocessor_response_time_bound_ideal_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN iarta_forall_sched". exact Logic.I. Qed.
Print Assumptions iarta_forall_sched.
Goal Logic.True. idtac "AUDIT_END iarta_forall_sched". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN iarta_forall_arr". exact Logic.I. Qed.
Print Assumptions iarta_forall_arr.
Goal Logic.True. idtac "AUDIT_END iarta_forall_arr". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN iarta_forall_state". exact Logic.I. Qed.
Print Assumptions iarta_forall_state.
Goal Logic.True. idtac "AUDIT_END iarta_forall_state". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN iarta_ideal_progress_rel". exact Logic.I. Qed.
Print Assumptions iarta_ideal_progress_rel.
Goal Logic.True. idtac "AUDIT_END iarta_ideal_progress_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN iarta_unit_service_rel". exact Logic.I. Qed.
Print Assumptions iarta_unit_service_rel.
Goal Logic.True. idtac "AUDIT_END iarta_unit_service_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN iarta_scheduled_at_related". exact Logic.I. Qed.
Print Assumptions iarta_scheduled_at_related.
Goal Logic.True. idtac "AUDIT_END iarta_scheduled_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN iarta_must_arrive_rel". exact Logic.I. Qed.
Print Assumptions iarta_must_arrive_rel.
Goal Logic.True. idtac "AUDIT_END iarta_must_arrive_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN iarta_completed_dont_execute_rel". exact Logic.I. Qed.
Print Assumptions iarta_completed_dont_execute_rel.
Goal Logic.True. idtac "AUDIT_END iarta_completed_dont_execute_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN iarta_np_fun_rel". exact Logic.I. Qed.
Print Assumptions iarta_np_fun_rel.
Goal Logic.True. idtac "AUDIT_END iarta_np_fun_rel". exact Logic.I. Qed.
