From FoundationCertificates Require Import
  PcoBaseAdapter PcoStaticOrder PcoDynamicOrder PriorityCoercionCorrespondence
  PriorityRateMonotonicCorrespondence.

Goal Logic.True. idtac "AUDIT_BEGIN RM_correspondence". exact Logic.I. Qed.
Print Assumptions RM_correspondence.
Goal Logic.True. idtac "AUDIT_END RM_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN RM_is_reflexive_correspondence". exact Logic.I. Qed.
Print Assumptions RM_is_reflexive_correspondence.
Goal Logic.True. idtac "AUDIT_END RM_is_reflexive_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN RM_is_transitive_correspondence". exact Logic.I. Qed.
Print Assumptions RM_is_transitive_correspondence.
Goal Logic.True. idtac "AUDIT_END RM_is_transitive_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN RM_is_total_correspondence". exact Logic.I. Qed.
Print Assumptions RM_is_total_correspondence.
Goal Logic.True. idtac "AUDIT_END RM_is_total_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN SporadicModel_source_total". exact Logic.I. Qed.
Print Assumptions SporadicModel_source_total.
Goal Logic.True. idtac "AUDIT_END SporadicModel_source_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN SporadicModel_target_total". exact Logic.I. Qed.
Print Assumptions SporadicModel_target_total.
Goal Logic.True. idtac "AUDIT_END SporadicModel_target_total". exact Logic.I. Qed.
