From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence ServiceInversionPredCorrespondence AbstractDefinitionsBaseAdapter ServiceBaseAdapter ServiceNatBoolOperations AbstractDefinitionsArrivalOperations AbstractDefinitionsClasses AbstractDefinitionsNatBoolOperations AbstractDefinitionsIntervalOperations AbstractDefinitionsOperations AbstractDefinitionsSums AbstractDefinitionsLogical ServiceIntervalOperations ServiceScheduleOperations AbstractDefinitionsPendingOperations AbstractDefinitionsTaskOperations AbstractDefinitionsBusyIntervalHelpers AbstractDefinitionsBusyInterval PriorityBaseAdapter ReadinessInterferenceCorrespondence ReadinessAwareCorrespondence ArrivalsCorrespondence InterferenceCorrespondence FactsReadinessInterferenceCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN no_hep_ready_implies_no_another_hep_interference_correspondence". exact Logic.I. Qed.
Print Assumptions no_hep_ready_implies_no_another_hep_interference_correspondence.
Goal Logic.True. idtac "AUDIT_END no_hep_ready_implies_no_another_hep_interference_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN no_hep_ready_implies_no_service_inversion_correspondence". exact Logic.I. Qed.
Print Assumptions no_hep_ready_implies_no_service_inversion_correspondence.
Goal Logic.True. idtac "AUDIT_END no_hep_ready_implies_no_service_inversion_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fri_scheduled_related". exact Logic.I. Qed.
Print Assumptions fri_scheduled_related.
Goal Logic.True. idtac "AUDIT_END fri_scheduled_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fri_valid_schedule_related". exact Logic.I. Qed.
Print Assumptions fri_valid_schedule_related.
Goal Logic.True. idtac "AUDIT_END fri_valid_schedule_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fri_forall_jlfp". exact Logic.I. Qed.
Print Assumptions fri_forall_jlfp.
Goal Logic.True. idtac "AUDIT_END fri_forall_jlfp". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fri_some_hep_job_ready_related". exact Logic.I. Qed.
Print Assumptions fri_some_hep_job_ready_related.
Goal Logic.True. idtac "AUDIT_END fri_some_hep_job_ready_related". exact Logic.I. Qed.
