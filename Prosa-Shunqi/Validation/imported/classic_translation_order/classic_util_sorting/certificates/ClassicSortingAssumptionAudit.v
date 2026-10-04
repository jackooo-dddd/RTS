From FoundationCertificates Require Import ClassicSortingCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN sort_ordered_correspondence". exact Logic.I. Qed.
Print Assumptions sort_ordered_correspondence.
Goal Logic.True. idtac "AUDIT_END sort_ordered_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sorted_rcons_prefix_correspondence". exact Logic.I. Qed.
Print Assumptions sorted_rcons_prefix_correspondence.
Goal Logic.True. idtac "AUDIT_END sorted_rcons_prefix_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN order_sorted_rcons_correspondence". exact Logic.I. Qed.
Print Assumptions order_sorted_rcons_correspondence.
Goal Logic.True. idtac "AUDIT_END order_sorted_rcons_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sorted_lt_idx_implies_rel_correspondence". exact Logic.I. Qed.
Print Assumptions sorted_lt_idx_implies_rel_correspondence.
Goal Logic.True. idtac "AUDIT_END sorted_lt_idx_implies_rel_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sorted_rel_implies_le_idx_correspondence". exact Logic.I. Qed.
Print Assumptions sorted_rel_implies_le_idx_correspondence.
Goal Logic.True. idtac "AUDIT_END sorted_rel_implies_le_idx_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN prev_le_next_correspondence". exact Logic.I. Qed.
Print Assumptions prev_le_next_correspondence.
Goal Logic.True. idtac "AUDIT_END prev_le_next_correspondence". exact Logic.I. Qed.
