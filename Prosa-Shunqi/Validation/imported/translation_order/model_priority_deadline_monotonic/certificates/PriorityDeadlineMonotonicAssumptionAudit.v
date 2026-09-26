From FoundationCertificates Require Import
  PcoBaseAdapter PcoStaticOrder PcoDynamicOrder PriorityCoercionCorrespondence
  PriorityDeadlineMonotonicCorrespondence.

Goal Logic.True. idtac "AUDIT_BEGIN DM_correspondence". exact Logic.I. Qed.
Print Assumptions DM_correspondence.
Goal Logic.True. idtac "AUDIT_END DM_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN DM_is_reflexive_correspondence". exact Logic.I. Qed.
Print Assumptions DM_is_reflexive_correspondence.
Goal Logic.True. idtac "AUDIT_END DM_is_reflexive_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN DM_is_transitive_correspondence". exact Logic.I. Qed.
Print Assumptions DM_is_transitive_correspondence.
Goal Logic.True. idtac "AUDIT_END DM_is_transitive_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN DM_is_total_correspondence". exact Logic.I. Qed.
Print Assumptions DM_is_total_correspondence.
Goal Logic.True. idtac "AUDIT_END DM_is_total_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN TaskDeadline_source_total". exact Logic.I. Qed.
Print Assumptions TaskDeadline_source_total.
Goal Logic.True. idtac "AUDIT_END TaskDeadline_source_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN TaskDeadline_target_total". exact Logic.I. Qed.
Print Assumptions TaskDeadline_target_total.
Goal Logic.True. idtac "AUDIT_END TaskDeadline_target_total". exact Logic.I. Qed.
