From FoundationCertificates Require Import PoetCertificate PoetTypeAudit.

Goal True.
  idtac "AUDIT_BEGIN forall_exists_implied_by_forall_in_zip".
  exact I.
Qed.
Print Assumptions forall_exists_implied_by_forall_in_zip_statement_certificate.
Goal True.
  idtac "AUDIT_END forall_exists_implied_by_forall_in_zip".
  exact I.
Qed.
