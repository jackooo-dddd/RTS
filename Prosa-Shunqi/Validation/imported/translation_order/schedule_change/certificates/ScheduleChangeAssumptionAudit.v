From FoundationCertificates Require Import
  ScheduleChangeStateAdapter ScheduleChangeOptionOperations
  ScheduleChangeIntervalOperations ScheduleChangeListOperations
  ScheduleChangeCorrespondence.

Goal True.
Proof.
  idtac "AUDIT_BEGIN scheduled_job_dependency".
  Print Assumptions sc_scheduled_job_correspondence.
  idtac "AUDIT_END scheduled_job_dependency".
  idtac "AUDIT_BEGIN option_ne_dependency".
  Print Assumptions sc_option_ne_correspondence.
  idtac "AUDIT_END option_ne_dependency".
  idtac "AUDIT_BEGIN index_iota_dependency".
  Print Assumptions sc_index_iota_related.
  idtac "AUDIT_END index_iota_dependency".
  idtac "AUDIT_BEGIN countP_dependency".
  Print Assumptions sc_countP_related.
  idtac "AUDIT_END countP_dependency".
  idtac "AUDIT_BEGIN all_dependency".
  Print Assumptions sc_all_related.
  idtac "AUDIT_END all_dependency".
  idtac "AUDIT_BEGIN schedule_change".
  Print Assumptions schedule_change_correspondence.
  idtac "AUDIT_END schedule_change".
  idtac "AUDIT_BEGIN number_schedule_changes".
  Print Assumptions number_schedule_changes_correspondence.
  idtac "AUDIT_END number_schedule_changes".
  idtac "AUDIT_BEGIN no_schedule_changes_during".
  Print Assumptions no_schedule_changes_during_correspondence.
  idtac "AUDIT_END no_schedule_changes_during".
  idtac "AUDIT_BEGIN scheduled_job_invariant".
  Print Assumptions scheduled_job_invariant_correspondence.
  idtac "AUDIT_END scheduled_job_invariant".
Abort.
