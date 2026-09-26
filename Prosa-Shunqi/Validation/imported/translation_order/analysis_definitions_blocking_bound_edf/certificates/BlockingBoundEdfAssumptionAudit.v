From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence TaskPreemptionParametersCorrespondence BlockingBoundEdfCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN blocking_relevant_correspondence". exact Logic.I. Qed.
Print Assumptions blocking_relevant_correspondence.
Goal Logic.True. idtac "AUDIT_END blocking_relevant_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN blocking_bound_correspondence". exact Logic.I. Qed.
Print Assumptions blocking_bound_correspondence.
Goal Logic.True. idtac "AUDIT_END blocking_bound_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbe_bigmax_canonical". exact Logic.I. Qed.
Print Assumptions bbe_bigmax_canonical.
Goal Logic.True. idtac "AUDIT_END bbe_bigmax_canonical". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbe_bigmax_related". exact Logic.I. Qed.
Print Assumptions bbe_bigmax_related.
Goal Logic.True. idtac "AUDIT_END bbe_bigmax_related". exact Logic.I. Qed.
