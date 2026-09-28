From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence PreemptionTimeCorrespondence PriorityDrivenCorrespondence PStateCoverHelpers FactsPreemptionHelpers WorkloadCorrespondence PriorityInversionCorrespondence ExistenceHelpers HepAtPtHelpers TaskPreemptionParametersCorrespondence BusyIntervalPiHelpers BlockingBoundFpFactsCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN nonpreemptive_segments_bounded_by_blocking_correspondence". exact Logic.I. Qed.
Print Assumptions nonpreemptive_segments_bounded_by_blocking_correspondence.
Goal Logic.True. idtac "AUDIT_END nonpreemptive_segments_bounded_by_blocking_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbfp_forall_list". exact Logic.I. Qed.
Print Assumptions bbfp_forall_list.
Goal Logic.True. idtac "AUDIT_END bbfp_forall_list". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbfp_forall_fp". exact Logic.I. Qed.
Print Assumptions bbfp_forall_fp.
Goal Logic.True. idtac "AUDIT_END bbfp_forall_fp". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbfp_fp_jlfp_rel". exact Logic.I. Qed.
Print Assumptions bbfp_fp_jlfp_rel.
Goal Logic.True. idtac "AUDIT_END bbfp_fp_jlfp_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbfp_blocking_bound_related". exact Logic.I. Qed.
Print Assumptions bbfp_blocking_bound_related.
Goal Logic.True. idtac "AUDIT_END bbfp_blocking_bound_related". exact Logic.I. Qed.
