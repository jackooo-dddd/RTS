From FoundationCertificates Require Import IdealBaseAdapter IdealCorrespondence.

Goal True.
Proof.
  idtac "AUDIT_BEGIN option_roundtrip".
  Print Assumptions ideal_option_target_roundtrip.
  idtac "AUDIT_END option_roundtrip".
  idtac "AUDIT_BEGIN scheduled_on".
  Print Assumptions ideal_scheduled_on_correspondence.
  idtac "AUDIT_END scheduled_on".
  idtac "AUDIT_BEGIN supply_on".
  Print Assumptions ideal_supply_on_correspondence.
  idtac "AUDIT_END supply_on".
  idtac "AUDIT_BEGIN service_on".
  Print Assumptions ideal_service_on_correspondence.
  idtac "AUDIT_END service_on".
  idtac "AUDIT_BEGIN processor_state".
  Print Assumptions ideal_processor_state_correspondence.
  idtac "AUDIT_END processor_state".
  idtac "AUDIT_BEGIN ideal_is_idle".
  Print Assumptions ideal_is_idle_correspondence.
  idtac "AUDIT_END ideal_is_idle".
Abort.
