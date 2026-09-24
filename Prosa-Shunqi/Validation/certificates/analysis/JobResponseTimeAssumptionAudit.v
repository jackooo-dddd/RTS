From FoundationCertificates Require Import
  ServiceBaseAdapter ServiceNatBoolOperations ServiceJobOperations
  ServiceCorrespondence JobResponseTimeCorrespondence.

Goal True.
Proof.
  idtac "AUDIT_BEGIN job_response_time_exceeds".
  Print Assumptions job_response_time_exceeds_correspondence.
  idtac "AUDIT_END job_response_time_exceeds".
  idtac "AUDIT_BEGIN completed_by_dependency".
  Print Assumptions completed_by_correspondence.
  idtac "AUDIT_END completed_by_dependency".
  idtac "AUDIT_BEGIN job_arrival_dependency".
  Print Assumptions svc_job_arrival_import.
  idtac "AUDIT_END job_arrival_dependency".
  idtac "AUDIT_BEGIN bool_not_dependency".
  Print Assumptions svc_bool_not_related.
  idtac "AUDIT_END bool_not_dependency".
Abort.
