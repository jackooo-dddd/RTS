From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence PreemptionTimeCorrespondence PriorityDrivenCorrespondence PStateCoverHelpers FactsPreemptionHelpers WorkloadCorrespondence PriorityInversionCorrespondence ExistenceHelpers BusyIntervalArrivalCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN busy_interval_prefix_job_arrival_correspondence". exact Logic.I. Qed.
Print Assumptions busy_interval_prefix_job_arrival_correspondence.
Goal Logic.True. idtac "AUDIT_END busy_interval_prefix_job_arrival_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN busy_interval_job_arrival_correspondence". exact Logic.I. Qed.
Print Assumptions busy_interval_job_arrival_correspondence.
Goal Logic.True. idtac "AUDIT_END busy_interval_job_arrival_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN busy_prefix_starts_when_hep_job_arrives_correspondence". exact Logic.I. Qed.
Print Assumptions busy_prefix_starts_when_hep_job_arrives_correspondence.
Goal Logic.True. idtac "AUDIT_END busy_prefix_starts_when_hep_job_arrives_correspondence". exact Logic.I. Qed.
