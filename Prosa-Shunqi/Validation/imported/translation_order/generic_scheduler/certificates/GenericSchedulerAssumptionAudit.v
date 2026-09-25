From FoundationCertificates Require Import
  GenericSchedulerBaseAdapter GenericSchedulerOperations
  GenericSchedulerRecursionEquations GenericSchedulerCorrespondence.

Goal True.
Proof.
  idtac "AUDIT_BEGIN PointwisePolicy".
  Print Assumptions gs_pointwise_policy_application.
  idtac "AUDIT_END PointwisePolicy".
  idtac "AUDIT_BEGIN empty_schedule".
  Print Assumptions gs_empty_schedule_correspondence.
  idtac "AUDIT_END empty_schedule".
  idtac "AUDIT_BEGIN schedule_up_to".
  Print Assumptions gs_prefix_correspondence.
  idtac "AUDIT_END schedule_up_to".
  idtac "AUDIT_BEGIN generic_schedule".
  Print Assumptions gs_generic_schedule_correspondence.
  idtac "AUDIT_END generic_schedule".
  idtac "AUDIT_BEGIN prefix_zero_equation".
  Print Assumptions gs_target_prefix_zero.
  idtac "AUDIT_END prefix_zero_equation".
  idtac "AUDIT_BEGIN prefix_succ_equation".
  Print Assumptions gs_target_prefix_succ.
  idtac "AUDIT_END prefix_succ_equation".
  idtac "AUDIT_BEGIN nat_equality".
  Print Assumptions gs_nat_beq_related.
  idtac "AUDIT_END nat_equality".
  idtac "AUDIT_BEGIN replace_at".
  Print Assumptions gs_replace_at_correspondence.
  idtac "AUDIT_END replace_at".
  idtac "AUDIT_BEGIN state_left_coverage".
  Print Assumptions gs_state_left_coverage.
  idtac "AUDIT_END state_left_coverage".
  idtac "AUDIT_BEGIN state_right_coverage".
  Print Assumptions gs_state_right_coverage.
  idtac "AUDIT_END state_right_coverage".
  idtac "AUDIT_BEGIN constant_policy_coverage".
  Print Assumptions gs_constant_policy_coverage.
  idtac "AUDIT_END constant_policy_coverage".
Abort.
