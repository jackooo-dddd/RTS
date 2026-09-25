From FoundationCertificates Require Import SpinBaseAdapter SpinCorrespondence.

Goal True.
Proof.
  idtac "AUDIT_BEGIN processor_state".
  Print Assumptions spin_state_type_correspondence.
  idtac "AUDIT_END processor_state".
  idtac "AUDIT_BEGIN spin_scheduled_on".
  Print Assumptions spin_scheduled_on_correspondence.
  idtac "AUDIT_END spin_scheduled_on".
  idtac "AUDIT_BEGIN spin_supply_on".
  Print Assumptions spin_supply_on_correspondence.
  idtac "AUDIT_END spin_supply_on".
  idtac "AUDIT_BEGIN spin_service_on".
  Print Assumptions spin_service_on_correspondence.
  idtac "AUDIT_END spin_service_on".
  idtac "AUDIT_BEGIN pstate_instance".
  Print Assumptions pstate_instance_correspondence.
  idtac "AUDIT_END pstate_instance".
Abort.
