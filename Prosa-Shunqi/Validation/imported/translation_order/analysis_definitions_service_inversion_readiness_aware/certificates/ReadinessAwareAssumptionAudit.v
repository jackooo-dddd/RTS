From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence ServiceInversionPredCorrespondence AbstractDefinitionsBaseAdapter ServiceBaseAdapter ServiceNatBoolOperations AbstractDefinitionsArrivalOperations AbstractDefinitionsClasses AbstractDefinitionsNatBoolOperations AbstractDefinitionsIntervalOperations AbstractDefinitionsOperations AbstractDefinitionsSums AbstractDefinitionsLogical ServiceIntervalOperations ServiceScheduleOperations AbstractDefinitionsPendingOperations AbstractDefinitionsTaskOperations AbstractDefinitionsBusyIntervalHelpers AbstractDefinitionsBusyInterval PriorityBaseAdapter ReadinessInterferenceCorrespondence ReadinessAwareCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN service_inversion_correspondence". exact Logic.I. Qed.
Print Assumptions service_inversion_correspondence.
Goal Logic.True. idtac "AUDIT_END service_inversion_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cumulative_service_inversion_correspondence". exact Logic.I. Qed.
Print Assumptions cumulative_service_inversion_correspondence.
Goal Logic.True. idtac "AUDIT_END cumulative_service_inversion_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_inversion_is_bounded_correspondence". exact Logic.I. Qed.
Print Assumptions service_inversion_is_bounded_correspondence.
Goal Logic.True. idtac "AUDIT_END service_inversion_is_bounded_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ra_jldp_related". exact Logic.I. Qed.
Print Assumptions ra_jldp_related.
Goal Logic.True. idtac "AUDIT_END ra_jldp_related". exact Logic.I. Qed.
