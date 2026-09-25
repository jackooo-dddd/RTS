From ReadinessBasicCertificates Require Import BasicPendingCorrespondence.

Goal True.
Proof.
  idtac "AUDIT_BEGIN basic_service_at".
  Print Assumptions basic_service_at_related.
  idtac "AUDIT_END basic_service_at".
  idtac "AUDIT_BEGIN basic_service_during".
  Print Assumptions basic_service_during_related.
  idtac "AUDIT_END basic_service_during".
  idtac "AUDIT_BEGIN basic_service".
  Print Assumptions basic_service_related.
  idtac "AUDIT_END basic_service".
  idtac "AUDIT_BEGIN basic_completed_by".
  Print Assumptions basic_completed_by_related.
  idtac "AUDIT_END basic_completed_by".
  idtac "AUDIT_BEGIN basic_pending".
  Print Assumptions basic_pending_related.
  idtac "AUDIT_END basic_pending".
  idtac "AUDIT_BEGIN basic_ready_field".
  Print Assumptions basic_ready_field_correspondence.
  idtac "AUDIT_END basic_ready_field".
  idtac "AUDIT_BEGIN basic_bool_implication".
  Print Assumptions basic_bool_implication_correspondence.
  idtac "AUDIT_END basic_bool_implication".
  idtac "AUDIT_BEGIN basic_ready_law".
  Print Assumptions basic_ready_law_statement_correspondence.
  idtac "AUDIT_END basic_ready_law".
Abort.
