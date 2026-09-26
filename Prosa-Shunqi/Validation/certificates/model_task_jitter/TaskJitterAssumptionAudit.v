From FoundationCertificates Require Import
  TaskJitterBaseAdapter TaskJitterCorrespondence.

Goal Logic.True. idtac "AUDIT_BEGIN TaskJitter_source_total". exact Logic.I. Qed.
Print Assumptions TaskJitter_source_total.
Goal Logic.True. idtac "AUDIT_END TaskJitter_source_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN TaskJitter_target_total". exact Logic.I. Qed.
Print Assumptions TaskJitter_target_total.
Goal Logic.True. idtac "AUDIT_END TaskJitter_target_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN TaskJitter_source_roundtrip". exact Logic.I. Qed.
Print Assumptions TaskJitter_source_roundtrip.
Goal Logic.True. idtac "AUDIT_END TaskJitter_source_roundtrip". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN valid_jitter_correspondence". exact Logic.I. Qed.
Print Assumptions valid_jitter_correspondence.
Goal Logic.True. idtac "AUDIT_END valid_jitter_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN valid_jitter_bounds_correspondence". exact Logic.I. Qed.
Print Assumptions valid_jitter_bounds_correspondence.
Goal Logic.True. idtac "AUDIT_END valid_jitter_bounds_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN tj_decide_mem_related". exact Logic.I. Qed.
Print Assumptions tj_decide_mem_related.
Goal Logic.True. idtac "AUDIT_END tj_decide_mem_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN tj_eq_correspondence". exact Logic.I. Qed.
Print Assumptions tj_eq_correspondence.
Goal Logic.True. idtac "AUDIT_END tj_eq_correspondence". exact Logic.I. Qed.
