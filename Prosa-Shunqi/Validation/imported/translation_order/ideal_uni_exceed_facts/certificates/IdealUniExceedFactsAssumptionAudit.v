From FoundationCertificates Require Import
  IdealUniExceedFactsModelCorrespondence
  IdealUniExceedFactsScheduledStatement
  IdealUniExceedFactsCorrespondence
  IdealUniExceedFactsBlackoutStatement.

Goal True.
Proof.
  idtac "AUDIT_BEGIN eps_is_unit_supply".
  Print Assumptions facts_unit_supply_model_correspondence.
  idtac "AUDIT_END eps_is_unit_supply".
  idtac "AUDIT_BEGIN scheduled_at_procstate".
  Print Assumptions facts_scheduled_at_procstate_statement_correspondence.
  idtac "AUDIT_END scheduled_at_procstate".
  idtac "AUDIT_BEGIN eps_is_uniproc".
  Print Assumptions facts_uniprocessor_model_correspondence.
  idtac "AUDIT_END eps_is_uniproc".
  idtac "AUDIT_BEGIN eps_is_fully_consuming".
  Print Assumptions facts_fully_consuming_model_correspondence.
  idtac "AUDIT_END eps_is_fully_consuming".
  idtac "AUDIT_BEGIN eps_is_unit_service".
  Print Assumptions facts_unit_service_model_correspondence.
  idtac "AUDIT_END eps_is_unit_service".
  idtac "AUDIT_BEGIN is_exceedance_exec".
  Print Assumptions facts_is_exceedance_exec_correspondence.
  idtac "AUDIT_END is_exceedance_exec".
  idtac "AUDIT_BEGIN blackout_implies_exceedance_execution".
  Print Assumptions facts_blackout_statement_correspondence.
  idtac "AUDIT_END blackout_implies_exceedance_execution".
Abort.
