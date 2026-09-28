From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence WorkloadCorrespondence AbstractDefinitionsBaseAdapter ServiceBaseAdapter ServiceNatBoolOperations AbstractDefinitionsArrivalOperations AbstractDefinitionsClasses AbstractDefinitionsNatBoolOperations AbstractDefinitionsIntervalOperations AbstractDefinitionsOperations AbstractDefinitionsSums AbstractDefinitionsLogical ServiceIntervalOperations ServiceScheduleOperations AbstractDefinitionsPendingOperations AbstractDefinitionsTaskOperations AbstractDefinitionsBusyIntervalHelpers AbstractRtaHelpers JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence TaskPreemptionParametersCorrespondence IdealAbstractRtaHelpers ArrivalSequenceBaseAdapter ArrivalSequenceOperations TaskScheduleCorrespondence CurvesCorrespondence RequestBoundFunctionCorrespondence SequentialityCorrespondence ServiceOfJobsCorrespondence SupplyScheduleBaseAdapter SupplyScheduleFiniteOperations SupplyScheduleOperations SupplyBaseAdapter SupplyNatBoolOperations SupplyIntervalOperations SupplyCorrespondence IbfTaskHelpers IbfSupplyTaskCorrespondence IbfTaskFullHelpers ServiceInversionPredCorrespondence InterferenceCorrespondence RsIwHelpers WorkloadBoundedCorrespondence ServiceInversionBusyPrefixCorrespondence TaskIntraInterferenceBoundCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN task_intra_IBF_correspondence". exact Logic.I. Qed.
Print Assumptions task_intra_IBF_correspondence.
Goal Logic.True. idtac "AUDIT_END task_intra_IBF_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN instantiated_task_intra_interference_is_bounded_correspondence". exact Logic.I. Qed.
Print Assumptions instantiated_task_intra_interference_is_bounded_correspondence.
Goal Logic.True. idtac "AUDIT_END instantiated_task_intra_interference_is_bounded_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN tiib_fun1_to_target_rel". exact Logic.I. Qed.
Print Assumptions tiib_fun1_to_target_rel.
Goal Logic.True. idtac "AUDIT_END tiib_fun1_to_target_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN tiib_fun1_to_source_rel". exact Logic.I. Qed.
Print Assumptions tiib_fun1_to_source_rel.
Goal Logic.True. idtac "AUDIT_END tiib_fun1_to_source_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN tiib_forall_fun1". exact Logic.I. Qed.
Print Assumptions tiib_forall_fun1.
Goal Logic.True. idtac "AUDIT_END tiib_forall_fun1". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN tiib_ibf_rel". exact Logic.I. Qed.
Print Assumptions tiib_ibf_rel.
Goal Logic.True. idtac "AUDIT_END tiib_ibf_rel". exact Logic.I. Qed.
