From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence WorkloadCorrespondence CurvesCorrespondence RequestBoundFunctionCorrespondence WorkloadBoundedCorrespondence EdfAthepBoundCorrespondence TaskPreemptionParametersCorrespondence BlockingBoundEdfCorrespondence SearchSpaceEdfCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN is_in_search_space_correspondence". exact Logic.I. Qed.
Print Assumptions is_in_search_space_correspondence.
Goal Logic.True. idtac "AUDIT_END is_in_search_space_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN search_space_sub_correspondence". exact Logic.I. Qed.
Print Assumptions search_space_sub_correspondence.
Goal Logic.True. idtac "AUDIT_END search_space_sub_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sse_false_correspondence". exact Logic.I. Qed.
Print Assumptions sse_false_correspondence.
Goal Logic.True. idtac "AUDIT_END sse_false_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sse_nat_neq_correspondence". exact Logic.I. Qed.
Print Assumptions sse_nat_neq_correspondence.
Goal Logic.True. idtac "AUDIT_END sse_nat_neq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sse_or_correspondence". exact Logic.I. Qed.
Print Assumptions sse_or_correspondence.
Goal Logic.True. idtac "AUDIT_END sse_or_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sse_and3_correspondence". exact Logic.I. Qed.
Print Assumptions sse_and3_correspondence.
Goal Logic.True. idtac "AUDIT_END sse_and3_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sse_decide_not". exact Logic.I. Qed.
Print Assumptions sse_decide_not.
Goal Logic.True. idtac "AUDIT_END sse_decide_not". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sse_nat_neqb_related". exact Logic.I. Qed.
Print Assumptions sse_nat_neqb_related.
Goal Logic.True. idtac "AUDIT_END sse_nat_neqb_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sse_has_canonical". exact Logic.I. Qed.
Print Assumptions sse_has_canonical.
Goal Logic.True. idtac "AUDIT_END sse_has_canonical". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sse_has_related". exact Logic.I. Qed.
Print Assumptions sse_has_related.
Goal Logic.True. idtac "AUDIT_END sse_has_related". exact Logic.I. Qed.
