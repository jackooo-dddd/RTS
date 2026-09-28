From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence WorkloadCorrespondence CurvesCorrespondence RequestBoundFunctionCorrespondence WorkloadBoundedCorrespondence SearchSpaceFifoCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN is_in_search_space_correspondence". exact Logic.I. Qed.
Print Assumptions is_in_search_space_correspondence.
Goal Logic.True. idtac "AUDIT_END is_in_search_space_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN search_space_sub_correspondence". exact Logic.I. Qed.
Print Assumptions search_space_sub_correspondence.
Goal Logic.True. idtac "AUDIT_END search_space_sub_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ssfi_false_correspondence". exact Logic.I. Qed.
Print Assumptions ssfi_false_correspondence.
Goal Logic.True. idtac "AUDIT_END ssfi_false_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ssfi_nat_neq_correspondence". exact Logic.I. Qed.
Print Assumptions ssfi_nat_neq_correspondence.
Goal Logic.True. idtac "AUDIT_END ssfi_nat_neq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ssfi_or_correspondence". exact Logic.I. Qed.
Print Assumptions ssfi_or_correspondence.
Goal Logic.True. idtac "AUDIT_END ssfi_or_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ssfi_and3_correspondence". exact Logic.I. Qed.
Print Assumptions ssfi_and3_correspondence.
Goal Logic.True. idtac "AUDIT_END ssfi_and3_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ssfi_decide_not". exact Logic.I. Qed.
Print Assumptions ssfi_decide_not.
Goal Logic.True. idtac "AUDIT_END ssfi_decide_not". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ssfi_nat_neqb_related". exact Logic.I. Qed.
Print Assumptions ssfi_nat_neqb_related.
Goal Logic.True. idtac "AUDIT_END ssfi_nat_neqb_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ssfi_has_canonical". exact Logic.I. Qed.
Print Assumptions ssfi_has_canonical.
Goal Logic.True. idtac "AUDIT_END ssfi_has_canonical". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ssfi_has_related". exact Logic.I. Qed.
Print Assumptions ssfi_has_related.
Goal Logic.True. idtac "AUDIT_END ssfi_has_related". exact Logic.I. Qed.
