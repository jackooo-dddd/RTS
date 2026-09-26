From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence TaskOffsetCorrespondence FactsModelOffsetCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN first_job_arrival_correspondence". exact Logic.I. Qed.
Print Assumptions first_job_arrival_correspondence.
Goal Logic.True. idtac "AUDIT_END first_job_arrival_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN max_offset_g_correspondence". exact Logic.I. Qed.
Print Assumptions max_offset_g_correspondence.
Goal Logic.True. idtac "AUDIT_END max_offset_g_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fmo_eq_correspondence". exact Logic.I. Qed.
Print Assumptions fmo_eq_correspondence.
Goal Logic.True. idtac "AUDIT_END fmo_eq_correspondence". exact Logic.I. Qed.
