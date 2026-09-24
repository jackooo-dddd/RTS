From FoundationCertificates Require Import JobPropertiesBaseAdapter
  JobPropertiesOperations JobPropertiesCorrespondence.

Goal True.
Proof.
  idtac "AUDIT_BEGIN adapter_membership".
  Print Assumptions jp_membership_correspondence.
  idtac "AUDIT_END adapter_membership".
  idtac "AUDIT_BEGIN arrives_in_dependency".
  Print Assumptions jp_arrives_in_related.
  idtac "AUDIT_END arrives_in_dependency".
  idtac "AUDIT_BEGIN job_cost_positive".
  Print Assumptions job_cost_positive_correspondence.
  idtac "AUDIT_END job_cost_positive".
  idtac "AUDIT_BEGIN arrivals_have_positive_job_costs".
  Print Assumptions arrivals_have_positive_job_costs_correspondence.
  idtac "AUDIT_END arrivals_have_positive_job_costs".
Abort.
