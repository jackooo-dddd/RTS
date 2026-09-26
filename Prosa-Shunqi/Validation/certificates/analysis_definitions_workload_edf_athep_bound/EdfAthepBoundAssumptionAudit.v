From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence RequestBoundFunctionCorrespondence EdfAthepBoundCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN bound_on_athep_workload_correspondence". exact Logic.I. Qed.
Print Assumptions bound_on_athep_workload_correspondence.
Goal Logic.True. idtac "AUDIT_END bound_on_athep_workload_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN eab_min_related". exact Logic.I. Qed.
Print Assumptions eab_min_related.
Goal Logic.True. idtac "AUDIT_END eab_min_related". exact Logic.I. Qed.
