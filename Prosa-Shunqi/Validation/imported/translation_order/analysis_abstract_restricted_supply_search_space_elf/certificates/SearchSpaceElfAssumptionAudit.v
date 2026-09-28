From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence WorkloadCorrespondence CurvesCorrespondence RequestBoundFunctionCorrespondence WorkloadBoundedCorrespondence EdfAthepBoundCorrespondence NatSubCorrespondence PcoBaseAdapter PcoStaticOrder PcoDynamicOrder PriorityCoercionCorrespondence PriorityGelHelpers PriorityElfHelpers ElfAthepBoundCorrespondence TaskPreemptionParametersCorrespondence BlockingBoundElfCorrespondence SearchSpaceElfCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN is_in_search_space_correspondence". exact Logic.I. Qed.
Print Assumptions is_in_search_space_correspondence.
Goal Logic.True. idtac "AUDIT_END is_in_search_space_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN search_space_sub_correspondence". exact Logic.I. Qed.
Print Assumptions search_space_sub_correspondence.
Goal Logic.True. idtac "AUDIT_END search_space_sub_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ssel_false_correspondence". exact Logic.I. Qed.
Print Assumptions ssel_false_correspondence.
Goal Logic.True. idtac "AUDIT_END ssel_false_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ssel_nat_neq_correspondence". exact Logic.I. Qed.
Print Assumptions ssel_nat_neq_correspondence.
Goal Logic.True. idtac "AUDIT_END ssel_nat_neq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ssel_or_correspondence". exact Logic.I. Qed.
Print Assumptions ssel_or_correspondence.
Goal Logic.True. idtac "AUDIT_END ssel_or_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ssel_and3_correspondence". exact Logic.I. Qed.
Print Assumptions ssel_and3_correspondence.
Goal Logic.True. idtac "AUDIT_END ssel_and3_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ssel_decide_not". exact Logic.I. Qed.
Print Assumptions ssel_decide_not.
Goal Logic.True. idtac "AUDIT_END ssel_decide_not". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ssel_nat_neqb_related". exact Logic.I. Qed.
Print Assumptions ssel_nat_neqb_related.
Goal Logic.True. idtac "AUDIT_END ssel_nat_neqb_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ssel_int_neq_le". exact Logic.I. Qed.
Print Assumptions ssel_int_neq_le.
Goal Logic.True. idtac "AUDIT_END ssel_int_neq_le". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ssel_int_neq_related". exact Logic.I. Qed.
Print Assumptions ssel_int_neq_related.
Goal Logic.True. idtac "AUDIT_END ssel_int_neq_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ssel_has_canonical". exact Logic.I. Qed.
Print Assumptions ssel_has_canonical.
Goal Logic.True. idtac "AUDIT_END ssel_has_canonical". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ssel_has_related". exact Logic.I. Qed.
Print Assumptions ssel_has_related.
Goal Logic.True. idtac "AUDIT_END ssel_has_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ssel_ep_task_related". exact Logic.I. Qed.
Print Assumptions ssel_ep_task_related.
Goal Logic.True. idtac "AUDIT_END ssel_ep_task_related". exact Logic.I. Qed.
