From FoundationCertificates Require Import
  PcoBaseAdapter PcoStaticOrder PcoDynamicOrder PriorityCoercionCorrespondence
  PriorityFifoCorrespondence.

Goal Logic.True. idtac "AUDIT_BEGIN FIFO_correspondence". exact Logic.I. Qed.
Print Assumptions FIFO_correspondence.
Goal Logic.True. idtac "AUDIT_END FIFO_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN FIFO_is_reflexive_correspondence". exact Logic.I. Qed.
Print Assumptions FIFO_is_reflexive_correspondence.
Goal Logic.True. idtac "AUDIT_END FIFO_is_reflexive_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN FIFO_is_transitive_correspondence". exact Logic.I. Qed.
Print Assumptions FIFO_is_transitive_correspondence.
Goal Logic.True. idtac "AUDIT_END FIFO_is_transitive_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN FIFO_is_total_correspondence". exact Logic.I. Qed.
Print Assumptions FIFO_is_total_correspondence.
Goal Logic.True. idtac "AUDIT_END FIFO_is_total_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN JobArrival_source_total". exact Logic.I. Qed.
Print Assumptions JobArrival_source_total.
Goal Logic.True. idtac "AUDIT_END JobArrival_source_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN JobArrival_target_total". exact Logic.I. Qed.
Print Assumptions JobArrival_target_total.
Goal Logic.True. idtac "AUDIT_END JobArrival_target_total". exact Logic.I. Qed.
