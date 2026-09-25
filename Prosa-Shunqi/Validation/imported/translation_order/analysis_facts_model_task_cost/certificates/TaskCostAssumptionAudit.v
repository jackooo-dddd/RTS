From FoundationCertificates Require Import
  TaskCostPositiveCorrespondence TaskCostSumCorrespondence.

Goal True.
Proof.
  idtac "AUDIT_BEGIN job_cost_positive_implies_task_cost_positive".
  Print Assumptions tc_positive_statement_correspondence.
  idtac "AUDIT_END job_cost_positive_implies_task_cost_positive".
  idtac "AUDIT_BEGIN sum_job_costs_bounded".
  Print Assumptions tc_sum_statement_correspondence.
  idtac "AUDIT_END sum_job_costs_bounded".
Abort.
