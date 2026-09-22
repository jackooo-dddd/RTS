From FoundationCertificates Require Import MinmaxCertificate MinmaxTypeAudit.

Goal True. idtac "AUDIT_BEGIN leq_bigmax_cond_seq". exact I. Qed.
Print Assumptions leq_bigmax_cond_seq_statement_certificate.
Goal True. idtac "AUDIT_END leq_bigmax_cond_seq". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN leq_bigmax_sup". exact I. Qed.
Print Assumptions leq_bigmax_sup_statement_certificate.
Goal True. idtac "AUDIT_END leq_bigmax_sup". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN bigmax_leq_seqP". exact I. Qed.
Print Assumptions bigmax_leq_seqP_statement_certificate.
Goal True. idtac "AUDIT_END bigmax_leq_seqP". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN leq_big_max". exact I. Qed.
Print Assumptions leq_big_max_statement_certificate.
Goal True. idtac "AUDIT_END leq_big_max". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN bigmax_ord_ltn_identity". exact I. Qed.
Print Assumptions bigmax_ord_ltn_identity_statement_certificate.
Goal True. idtac "AUDIT_END bigmax_ord_ltn_identity". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN bigmax_ltn_ord". exact I. Qed.
Print Assumptions bigmax_ltn_ord_statement_certificate.
Goal True. idtac "AUDIT_END bigmax_ltn_ord". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN bigmax_pred". exact I. Qed.
Print Assumptions bigmax_pred_statement_certificate.
Goal True. idtac "AUDIT_END bigmax_pred". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN bigmax_witness". exact I. Qed.
Print Assumptions bigmax_witness_statement_certificate.
Goal True. idtac "AUDIT_END bigmax_witness". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN bigmax_witness_diff". exact I. Qed.
Print Assumptions bigmax_witness_diff_statement_certificate.
Goal True. idtac "AUDIT_END bigmax_witness_diff". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN bigmax_subset". exact I. Qed.
Print Assumptions bigmax_subset_statement_certificate.
Goal True. idtac "AUDIT_END bigmax_subset". exact I. Qed.
