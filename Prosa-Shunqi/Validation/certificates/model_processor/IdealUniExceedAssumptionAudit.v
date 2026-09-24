From FoundationCertificates Require Import
  IdealUniExceedBaseAdapter IdealUniExceedSourceOperations
  IdealUniExceedCorrespondence.

Goal True.
Proof.
  idtac "AUDIT_BEGIN exceedance_processor_state".
  Print Assumptions iue_target_roundtrip.
  idtac "AUDIT_END exceedance_processor_state".
  idtac "AUDIT_BEGIN exceedance_processor_state_eqdef".
  Print Assumptions iue_eqdef_correspondence.
  idtac "AUDIT_END exceedance_processor_state_eqdef".
  idtac "AUDIT_BEGIN eqn_exceedance_processor_state".
  Print Assumptions iue_eqn_statement_correspondence.
  idtac "AUDIT_END eqn_exceedance_processor_state".
  idtac "AUDIT_BEGIN exceedance_scheduled_on".
  Print Assumptions iue_scheduled_on_correspondence.
  idtac "AUDIT_END exceedance_scheduled_on".
  idtac "AUDIT_BEGIN exceedance_supply_on".
  Print Assumptions iue_supply_on_correspondence.
  idtac "AUDIT_END exceedance_supply_on".
  idtac "AUDIT_BEGIN exceedance_service_on".
  Print Assumptions iue_service_on_correspondence.
  idtac "AUDIT_END exceedance_service_on".
  idtac "AUDIT_BEGIN exceedance_proc_state".
  Print Assumptions iue_processor_state_correspondence.
  idtac "AUDIT_END exceedance_proc_state".
Abort.
