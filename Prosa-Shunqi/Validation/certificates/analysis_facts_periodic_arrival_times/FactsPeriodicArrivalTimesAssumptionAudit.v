From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence TaskOffsetCorrespondence PeriodicCorrespondence FactsPeriodicArrivalTimesCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN periodic_arrival_times_correspondence". exact Logic.I. Qed.
Print Assumptions periodic_arrival_times_correspondence.
Goal Logic.True. idtac "AUDIT_END periodic_arrival_times_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_arrival_times_correspondence". exact Logic.I. Qed.
Print Assumptions job_arrival_times_correspondence.
Goal Logic.True. idtac "AUDIT_END job_arrival_times_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_arr_index_correspondence". exact Logic.I. Qed.
Print Assumptions job_arr_index_correspondence.
Goal Logic.True. idtac "AUDIT_END job_arr_index_correspondence". exact Logic.I. Qed.
