From FoundationCertificates Require Import
  PcoBaseAdapter PcoStaticOrder PcoDynamicOrder PriorityCoercionCorrespondence
  PriorityEdfCorrespondence.

Goal Logic.True. idtac "AUDIT_BEGIN EDF_correspondence". exact Logic.I. Qed.
Print Assumptions EDF_correspondence.
Goal Logic.True. idtac "AUDIT_END EDF_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN EDF_is_reflexive_correspondence". exact Logic.I. Qed.
Print Assumptions EDF_is_reflexive_correspondence.
Goal Logic.True. idtac "AUDIT_END EDF_is_reflexive_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN EDF_is_transitive_correspondence". exact Logic.I. Qed.
Print Assumptions EDF_is_transitive_correspondence.
Goal Logic.True. idtac "AUDIT_END EDF_is_transitive_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN EDF_is_total_correspondence". exact Logic.I. Qed.
Print Assumptions EDF_is_total_correspondence.
Goal Logic.True. idtac "AUDIT_END EDF_is_total_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN JobDeadline_source_total". exact Logic.I. Qed.
Print Assumptions JobDeadline_source_total.
Goal Logic.True. idtac "AUDIT_END JobDeadline_source_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN JobDeadline_target_total". exact Logic.I. Qed.
Print Assumptions JobDeadline_target_total.
Goal Logic.True. idtac "AUDIT_END JobDeadline_target_total". exact Logic.I. Qed.
