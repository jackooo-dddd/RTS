From FoundationCertificates Require Import
  PcoBaseAdapter PcoStaticOrder PcoDynamicOrder PriorityCoercionCorrespondence
  PriorityNumericFixedPriorityCorrespondence.

Goal Logic.True. idtac "AUDIT_BEGIN NFPA_is_reflexive_correspondence". exact Logic.I. Qed.
Print Assumptions NFPA_is_reflexive_correspondence.
Goal Logic.True. idtac "AUDIT_END NFPA_is_reflexive_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN NFPA_is_transitive_correspondence". exact Logic.I. Qed.
Print Assumptions NFPA_is_transitive_correspondence.
Goal Logic.True. idtac "AUDIT_END NFPA_is_transitive_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN NFPA_is_total_correspondence". exact Logic.I. Qed.
Print Assumptions NFPA_is_total_correspondence.
Goal Logic.True. idtac "AUDIT_END NFPA_is_total_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN NFPD_is_reflexive_correspondence". exact Logic.I. Qed.
Print Assumptions NFPD_is_reflexive_correspondence.
Goal Logic.True. idtac "AUDIT_END NFPD_is_reflexive_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN NFPD_is_transitive_correspondence". exact Logic.I. Qed.
Print Assumptions NFPD_is_transitive_correspondence.
Goal Logic.True. idtac "AUDIT_END NFPD_is_transitive_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN NFPD_is_total_correspondence". exact Logic.I. Qed.
Print Assumptions NFPD_is_total_correspondence.
Goal Logic.True. idtac "AUDIT_END NFPD_is_total_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN TaskPriority_source_total". exact Logic.I. Qed.
Print Assumptions TaskPriority_source_total.
Goal Logic.True. idtac "AUDIT_END TaskPriority_source_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN TaskPriority_target_total". exact Logic.I. Qed.
Print Assumptions TaskPriority_target_total.
Goal Logic.True. idtac "AUDIT_END TaskPriority_target_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN NumericFPAscending_correspondence". exact Logic.I. Qed.
Print Assumptions NumericFPAscending_correspondence.
Goal Logic.True. idtac "AUDIT_END NumericFPAscending_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN NumericFPDescending_correspondence". exact Logic.I. Qed.
Print Assumptions NumericFPDescending_correspondence.
Goal Logic.True. idtac "AUDIT_END NumericFPDescending_correspondence". exact Logic.I. Qed.
