From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence PreemptionTimeCorrespondence PriorityDrivenCorrespondence PStateCoverHelpers FactsPreemptionHelpers FactsPrioritySequentialCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN early_hep_job_is_scheduled_correspondence". exact Logic.I. Qed.
Print Assumptions early_hep_job_is_scheduled_correspondence.
Goal Logic.True. idtac "AUDIT_END early_hep_job_is_scheduled_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fps_exists_identity". exact Logic.I. Qed.
Print Assumptions fps_exists_identity.
Goal Logic.True. idtac "AUDIT_END fps_exists_identity". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fps_transitive_rel". exact Logic.I. Qed.
Print Assumptions fps_transitive_rel.
Goal Logic.True. idtac "AUDIT_END fps_transitive_rel". exact Logic.I. Qed.
