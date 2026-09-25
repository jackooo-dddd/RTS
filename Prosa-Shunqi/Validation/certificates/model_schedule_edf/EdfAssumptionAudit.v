From FoundationCertificates Require Import EdfOperations EdfCorrespondence.

Goal True.
Proof.
  idtac "AUDIT_BEGIN scheduled_in_dependency".
  Print Assumptions edf_scheduled_in_truth.
  idtac "AUDIT_END scheduled_in_dependency".
  idtac "AUDIT_BEGIN scheduled_at_dependency".
  Print Assumptions edf_scheduled_at_truth.
  idtac "AUDIT_END scheduled_at_dependency".
  idtac "AUDIT_BEGIN EDF_at".
  Print Assumptions EDF_at_correspondence.
  idtac "AUDIT_END EDF_at".
  idtac "AUDIT_BEGIN EDF_schedule".
  Print Assumptions EDF_schedule_correspondence.
  idtac "AUDIT_END EDF_schedule".
Abort.
