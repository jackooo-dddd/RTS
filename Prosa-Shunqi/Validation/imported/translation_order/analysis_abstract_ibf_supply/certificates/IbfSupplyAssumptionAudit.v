From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence WorkloadCorrespondence AbstractDefinitionsBaseAdapter ServiceBaseAdapter ServiceNatBoolOperations AbstractDefinitionsArrivalOperations AbstractDefinitionsClasses AbstractDefinitionsNatBoolOperations AbstractDefinitionsIntervalOperations AbstractDefinitionsOperations AbstractDefinitionsSums AbstractDefinitionsLogical ServiceIntervalOperations ServiceScheduleOperations AbstractDefinitionsPendingOperations AbstractDefinitionsTaskOperations AbstractDefinitionsBusyIntervalHelpers AbstractRtaHelpers SupplyScheduleBaseAdapter SupplyScheduleFiniteOperations SupplyScheduleOperations SupplyBaseAdapter SupplyNatBoolOperations SupplyIntervalOperations SupplyCorrespondence IbfSupplyCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN intra_interference_correspondence". exact Logic.I. Qed.
Print Assumptions intra_interference_correspondence.
Goal Logic.True. idtac "AUDIT_END intra_interference_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cumul_intra_interference_correspondence". exact Logic.I. Qed.
Print Assumptions cumul_intra_interference_correspondence.
Goal Logic.True. idtac "AUDIT_END cumul_intra_interference_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN intra_interference_is_bounded_by_correspondence". exact Logic.I. Qed.
Print Assumptions intra_interference_is_bounded_by_correspondence.
Goal Logic.True. idtac "AUDIT_END intra_interference_is_bounded_by_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ibfs_supply_pred_rel". exact Logic.I. Qed.
Print Assumptions ibfs_supply_pred_rel.
Goal Logic.True. idtac "AUDIT_END ibfs_supply_pred_rel". exact Logic.I. Qed.
