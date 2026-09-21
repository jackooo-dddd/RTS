From FoundationCertificates Require Import ListBatch5Operations
  ListBatch5Certificate.

Goal True. idtac "AUDIT_BEGIN bridge_nat_map". exact I. Qed.
Print Assumptions l5_nat_map_related.
Goal True. idtac "AUDIT_END bridge_nat_map". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN bridge_countP". exact I. Qed.
Print Assumptions l5_countP_related.
Goal True. idtac "AUDIT_END bridge_countP". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN bridge_nat_countP". exact I. Qed.
Print Assumptions l5_nat_countP_related.
Goal True. idtac "AUDIT_END bridge_nat_countP". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN index_iota_filter_step". exact I. Qed.
Print Assumptions index_iota_filter_step_statement_certificate.
Goal True. idtac "AUDIT_END index_iota_filter_step". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN range_iota_filter_step". exact I. Qed.
Print Assumptions range_iota_filter_step_statement_certificate.
Goal True. idtac "AUDIT_END range_iota_filter_step". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN iota_filter_gt". exact I. Qed.
Print Assumptions iota_filter_gt_statement_certificate.
Goal True. idtac "AUDIT_END iota_filter_gt". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN sub_count_seq". exact I. Qed.
Print Assumptions sub_count_seq_statement_certificate.
Goal True. idtac "AUDIT_END sub_count_seq". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN count_predUI'". exact I. Qed.
Print Assumptions count_predUI_statement_certificate.
Goal True. idtac "AUDIT_END count_predUI'". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN prefix_of". exact I. Qed.
Print Assumptions prefix_of_definition_certificate.
Goal True. idtac "AUDIT_END prefix_of". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN strict_prefix_of". exact I. Qed.
Print Assumptions strict_prefix_of_definition_certificate.
Goal True. idtac "AUDIT_END strict_prefix_of". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN shift_points_pos". exact I. Qed.
Print Assumptions shift_points_pos_definition_certificate.
Goal True. idtac "AUDIT_END shift_points_pos". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN shift_points_neg". exact I. Qed.
Print Assumptions shift_points_neg_definition_certificate.
Goal True. idtac "AUDIT_END shift_points_neg". exact I. Qed.
