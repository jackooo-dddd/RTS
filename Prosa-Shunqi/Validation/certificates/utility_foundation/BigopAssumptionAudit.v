From FoundationCertificates Require Import BigopCertificate BigopTypeAudit.

Goal True. idtac "AUDIT_BEGIN big_pred1_seq". exact I. Qed.
Print Assumptions big_pred1_seq_statement_certificate.
Goal True. idtac "AUDIT_END big_pred1_seq". exact I. Qed.
