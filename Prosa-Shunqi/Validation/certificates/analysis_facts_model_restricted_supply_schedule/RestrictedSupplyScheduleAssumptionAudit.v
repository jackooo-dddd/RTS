From FoundationCertificates Require Import
  RestrictedSupplyScheduleExactTypeGuards
  RestrictedSupplyScheduleModelCorrespondence.

Goal True.
Proof.
  idtac "AUDIT_BEGIN rs_proc_model_is_a_uniprocessor_model".
  Print Assumptions facts_uniprocessor_model_correspondence.
  idtac "AUDIT_END rs_proc_model_is_a_uniprocessor_model".
  idtac "AUDIT_BEGIN rs_proc_is_unit_supply".
  Print Assumptions facts_unit_supply_model_correspondence.
  idtac "AUDIT_END rs_proc_is_unit_supply".
  idtac "AUDIT_BEGIN rs_proc_model_fully_consuming".
  Print Assumptions facts_fully_consuming_model_correspondence.
  idtac "AUDIT_END rs_proc_model_fully_consuming".
Abort.
