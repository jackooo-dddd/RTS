From FoundationCertificates Require Import
  FtdmaBaseAdapter FtdmaArithmeticAdapter FtdmaSeqsetAdapter FtdmaPolicyAdapter FtdmaValidityCorrespondence FtdmaNumericCorrespondence FactsTdmaCorrespondence.

Goal Logic.True. idtac "AUDIT_BEGIN TDMA_cycle_ge_each_time_slot_correspondence". exact Logic.I. Qed.
Print Assumptions TDMA_cycle_ge_each_time_slot_correspondence.
Goal Logic.True. idtac "AUDIT_END TDMA_cycle_ge_each_time_slot_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN TDMA_cycle_positive_correspondence". exact Logic.I. Qed.
Print Assumptions TDMA_cycle_positive_correspondence.
Goal Logic.True. idtac "AUDIT_END TDMA_cycle_positive_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Offset_lt_cycle_correspondence". exact Logic.I. Qed.
Print Assumptions Offset_lt_cycle_correspondence.
Goal Logic.True. idtac "AUDIT_END Offset_lt_cycle_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Offset_add_slot_leq_cycle_correspondence". exact Logic.I. Qed.
Print Assumptions Offset_add_slot_leq_cycle_correspondence.
Goal Logic.True. idtac "AUDIT_END Offset_add_slot_leq_cycle_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN relation_offset_correspondence". exact Logic.I. Qed.
Print Assumptions relation_offset_correspondence.
Goal Logic.True. idtac "AUDIT_END relation_offset_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN task_in_time_slot_uniq_correspondence". exact Logic.I. Qed.
Print Assumptions task_in_time_slot_uniq_correspondence.
Goal Logic.True. idtac "AUDIT_END task_in_time_slot_uniq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ft_mem". exact Logic.I. Qed.
Print Assumptions ft_mem.
Goal Logic.True. idtac "AUDIT_END ft_mem". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ft_forall_nat". exact Logic.I. Qed.
Print Assumptions ft_forall_nat.
Goal Logic.True. idtac "AUDIT_END ft_forall_nat". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ft_eq". exact Logic.I. Qed.
Print Assumptions ft_eq.
Goal Logic.True. idtac "AUDIT_END ft_eq". exact Logic.I. Qed.
