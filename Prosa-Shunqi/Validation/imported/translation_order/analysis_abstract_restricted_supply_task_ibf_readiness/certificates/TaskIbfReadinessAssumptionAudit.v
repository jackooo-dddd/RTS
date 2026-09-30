From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence WorkloadCorrespondence AbstractDefinitionsBaseAdapter ServiceBaseAdapter ServiceNatBoolOperations AbstractDefinitionsArrivalOperations AbstractDefinitionsClasses AbstractDefinitionsNatBoolOperations AbstractDefinitionsIntervalOperations AbstractDefinitionsOperations AbstractDefinitionsSums AbstractDefinitionsLogical ServiceIntervalOperations ServiceScheduleOperations AbstractDefinitionsPendingOperations AbstractDefinitionsTaskOperations AbstractDefinitionsBusyIntervalHelpers AbstractRtaHelpers JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence TaskPreemptionParametersCorrespondence IdealAbstractRtaHelpers ArrivalSequenceBaseAdapter ArrivalSequenceOperations TaskScheduleCorrespondence CurvesCorrespondence RequestBoundFunctionCorrespondence SequentialityCorrespondence ServiceOfJobsCorrespondence SupplyScheduleBaseAdapter SupplyScheduleFiniteOperations SupplyScheduleOperations SupplyBaseAdapter SupplyNatBoolOperations SupplyIntervalOperations SupplyCorrespondence IbfTaskHelpers IbfSupplyTaskCorrespondence IbfTaskFullHelpers ServiceInversionPredCorrespondence InterferenceCorrespondence AbstractDefinitionsBusyInterval PriorityBaseAdapter ReadinessInterferenceCorrespondence ReadinessAwareCorrespondence IwReadinessCorrespondence WorkloadBoundedCorrespondence TaskIbfReadinessCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN task_intra_IBF_correspondence". exact Logic.I. Qed.
Print Assumptions task_intra_IBF_correspondence.
Goal Logic.True. idtac "AUDIT_END task_intra_IBF_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN instantiated_task_intra_interference_is_bounded_correspondence". exact Logic.I. Qed.
Print Assumptions instantiated_task_intra_interference_is_bounded_correspondence.
Goal Logic.True. idtac "AUDIT_END instantiated_task_intra_interference_is_bounded_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN tibfr_fun1_to_target_rel". exact Logic.I. Qed.
Print Assumptions tibfr_fun1_to_target_rel.
Goal Logic.True. idtac "AUDIT_END tibfr_fun1_to_target_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN tibfr_fun1_to_source_rel". exact Logic.I. Qed.
Print Assumptions tibfr_fun1_to_source_rel.
Goal Logic.True. idtac "AUDIT_END tibfr_fun1_to_source_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN tibfr_forall_fun1". exact Logic.I. Qed.
Print Assumptions tibfr_forall_fun1.
Goal Logic.True. idtac "AUDIT_END tibfr_forall_fun1". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN tibfr_reorder". exact Logic.I. Qed.
Print Assumptions tibfr_reorder.
Goal Logic.True. idtac "AUDIT_END tibfr_reorder". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN tibfr_ibf_rel". exact Logic.I. Qed.
Print Assumptions tibfr_ibf_rel.
Goal Logic.True. idtac "AUDIT_END tibfr_ibf_rel". exact Logic.I. Qed.
