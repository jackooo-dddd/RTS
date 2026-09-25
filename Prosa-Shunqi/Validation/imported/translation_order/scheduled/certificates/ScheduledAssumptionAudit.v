From FoundationCertificates Require Import ReadyArrivalOperations
  ReadyArrivalCorrespondence ScheduledStateOperations
  ScheduledCorrespondence.

Goal True.
Proof.
  idtac "AUDIT_BEGIN arrivals_up_to_dependency".
  Print Assumptions arrivals_up_to_correspondence_certificate.
  idtac "AUDIT_END arrivals_up_to_dependency".
  idtac "AUDIT_BEGIN filter_dependency".
  Print Assumptions ar_filter_related.
  idtac "AUDIT_END filter_dependency".
  idtac "AUDIT_BEGIN scheduled_in_dependency".
  Print Assumptions edf_scheduled_in_truth.
  idtac "AUDIT_END scheduled_in_dependency".
  idtac "AUDIT_BEGIN scheduled_at_dependency".
  Print Assumptions edf_scheduled_at_truth.
  idtac "AUDIT_END scheduled_at_dependency".
  idtac "AUDIT_BEGIN head_dependency".
  Print Assumptions scheduled_ohead_correspondence.
  idtac "AUDIT_END head_dependency".
  idtac "AUDIT_BEGIN empty_dependency".
  Print Assumptions scheduled_nil_eq_isEmpty_correspondence.
  idtac "AUDIT_END empty_dependency".
  idtac "AUDIT_BEGIN scheduled_jobs_at".
  Print Assumptions scheduled_jobs_at_correspondence.
  idtac "AUDIT_END scheduled_jobs_at".
  idtac "AUDIT_BEGIN scheduled_job_at".
  Print Assumptions scheduled_job_at_correspondence.
  idtac "AUDIT_END scheduled_job_at".
  idtac "AUDIT_BEGIN is_idle".
  Print Assumptions is_idle_correspondence.
  idtac "AUDIT_END is_idle".
Abort.
