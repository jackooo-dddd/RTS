From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence TaskPreemptionParametersCorrespondence RequestBoundFunctionCorrespondence EdfPiBoundCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN longest_busy_interval_with_pi_correspondence". exact Logic.I. Qed.
Print Assumptions longest_busy_interval_with_pi_correspondence.
Goal Logic.True. idtac "AUDIT_END longest_busy_interval_with_pi_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN epi_bigmax_canonical". exact Logic.I. Qed.
Print Assumptions epi_bigmax_canonical.
Goal Logic.True. idtac "AUDIT_END epi_bigmax_canonical". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN epi_bigmax_related". exact Logic.I. Qed.
Print Assumptions epi_bigmax_related.
Goal Logic.True. idtac "AUDIT_END epi_bigmax_related". exact Logic.I. Qed.
