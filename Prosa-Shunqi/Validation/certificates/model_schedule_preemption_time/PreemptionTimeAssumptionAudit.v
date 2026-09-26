From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence PreemptionTimeCorrespondence.

Goal Logic.True. idtac "AUDIT_BEGIN preemption_time_correspondence". exact Logic.I. Qed.
Print Assumptions preemption_time_correspondence.
Goal Logic.True. idtac "AUDIT_END preemption_time_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN spt_scheduled_jobs_related". exact Logic.I. Qed.
Print Assumptions spt_scheduled_jobs_related.
Goal Logic.True. idtac "AUDIT_END spt_scheduled_jobs_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN spt_case". exact Logic.I. Qed.
Print Assumptions spt_case.
Goal Logic.True. idtac "AUDIT_END spt_case". exact Logic.I. Qed.
