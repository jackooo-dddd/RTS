From FoundationCertificates Require Import ListBatch2Certificate.

Goal True. idtac "AUDIT_BEGIN filter_in_pred0". exact I. Qed.
Print Assumptions filter_in_pred0_statement_certificate.
Goal True. idtac "AUDIT_END filter_in_pred0". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN rem_all". exact I. Qed.
Print Assumptions rem_all_recursive_certificate.
Goal True. idtac "AUDIT_END rem_all". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN nin_rem_all". exact I. Qed.
Print Assumptions nin_rem_all_statement_certificate.
Goal True. idtac "AUDIT_END nin_rem_all". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN in_rem_all". exact I. Qed.
Print Assumptions in_rem_all_statement_certificate.
Goal True. idtac "AUDIT_END in_rem_all". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN rem_lt_id". exact I. Qed.
Print Assumptions rem_lt_id_statement_certificate.
Goal True. idtac "AUDIT_END rem_lt_id". exact I. Qed.
