From FoundationCertificates Require Import ListBatch3Certificate.

Goal True. idtac "AUDIT_BEGIN subseq_leq_size". exact I. Qed.
Print Assumptions subseq_leq_size_statement_certificate.
Goal True. idtac "AUDIT_END subseq_leq_size". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN in_zip". exact I. Qed.
Print Assumptions in_zip_statement_certificate.
Goal True. idtac "AUDIT_END in_zip". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN eq_ind_in_seq". exact I. Qed.
Print Assumptions eq_ind_in_seq_statement_certificate.
Goal True. idtac "AUDIT_END eq_ind_in_seq". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN default_or_in". exact I. Qed.
Print Assumptions default_or_in_statement_certificate.
Goal True. idtac "AUDIT_END default_or_in". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN exists_two". exact I. Qed.
Print Assumptions exists_two_statement_certificate.
Goal True. idtac "AUDIT_END exists_two". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN has_all_nilp". exact I. Qed.
Print Assumptions has_all_nilp_statement_certificate.
Goal True. idtac "AUDIT_END has_all_nilp". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN sorted_split". exact I. Qed.
Print Assumptions sorted_split_statement_certificate.
Goal True. idtac "AUDIT_END sorted_split". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN sorted_cat". exact I. Qed.
Print Assumptions sorted_cat_statement_certificate.
Goal True. idtac "AUDIT_END sorted_cat". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN nonnil_last". exact I. Qed.
Print Assumptions nonnil_last_statement_certificate.
Goal True. idtac "AUDIT_END nonnil_last". exact I. Qed.
