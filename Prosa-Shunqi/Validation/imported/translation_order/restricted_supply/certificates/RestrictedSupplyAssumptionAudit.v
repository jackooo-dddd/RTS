From FoundationCertificates Require Import
  RestrictedSupplyBaseAdapter RestrictedSupplyCorrespondence.

Goal True.
Proof.
  idtac "AUDIT_BEGIN processor_state".
  Print Assumptions rs_state_type_correspondence.
  idtac "AUDIT_END processor_state".
  idtac "AUDIT_BEGIN rs_scheduled_on".
  Print Assumptions rs_scheduled_on_correspondence.
  idtac "AUDIT_END rs_scheduled_on".
  idtac "AUDIT_BEGIN rs_supply_on".
  Print Assumptions rs_supply_on_correspondence.
  idtac "AUDIT_END rs_supply_on".
  idtac "AUDIT_BEGIN rs_service_on".
  Print Assumptions rs_service_on_correspondence.
  idtac "AUDIT_END rs_service_on".
  idtac "AUDIT_BEGIN rs_processor_state".
  Print Assumptions rs_processor_state_correspondence.
  idtac "AUDIT_END rs_processor_state".
Abort.
