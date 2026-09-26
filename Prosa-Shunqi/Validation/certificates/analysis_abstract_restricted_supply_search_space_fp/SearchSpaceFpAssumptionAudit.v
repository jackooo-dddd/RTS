From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence WorkloadCorrespondence CurvesCorrespondence RequestBoundFunctionCorrespondence WorkloadBoundedCorrespondence TaskPreemptionParametersCorrespondence BlockingBoundFpCorrespondence SearchSpaceFpCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN is_in_search_space_correspondence". exact Logic.I. Qed.
Print Assumptions is_in_search_space_correspondence.
Goal Logic.True. idtac "AUDIT_END is_in_search_space_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN search_space_sub_correspondence". exact Logic.I. Qed.
Print Assumptions search_space_sub_correspondence.
Goal Logic.True. idtac "AUDIT_END search_space_sub_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ssfp_false_correspondence". exact Logic.I. Qed.
Print Assumptions ssfp_false_correspondence.
Goal Logic.True. idtac "AUDIT_END ssfp_false_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ssfp_nat_neq_correspondence". exact Logic.I. Qed.
Print Assumptions ssfp_nat_neq_correspondence.
Goal Logic.True. idtac "AUDIT_END ssfp_nat_neq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ssfp_or_correspondence". exact Logic.I. Qed.
Print Assumptions ssfp_or_correspondence.
Goal Logic.True. idtac "AUDIT_END ssfp_or_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ssfp_and3_correspondence". exact Logic.I. Qed.
Print Assumptions ssfp_and3_correspondence.
Goal Logic.True. idtac "AUDIT_END ssfp_and3_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ssfp_decide_not". exact Logic.I. Qed.
Print Assumptions ssfp_decide_not.
Goal Logic.True. idtac "AUDIT_END ssfp_decide_not". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ssfp_nat_neqb_related". exact Logic.I. Qed.
Print Assumptions ssfp_nat_neqb_related.
Goal Logic.True. idtac "AUDIT_END ssfp_nat_neqb_related". exact Logic.I. Qed.
