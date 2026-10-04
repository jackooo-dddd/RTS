From FoundationCertificates Require Import ClassicUniLastExecutionCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN LastExecution_time_after_last_execution_correspondence". exact Logic.I. Qed.
Print Assumptions LastExecution_time_after_last_execution_correspondence.
Goal Logic.True. idtac "AUDIT_END LastExecution_time_after_last_execution_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN LastExecution_last_execution_after_arrival_correspondence". exact Logic.I. Qed.
Print Assumptions LastExecution_last_execution_after_arrival_correspondence.
Goal Logic.True. idtac "AUDIT_END LastExecution_last_execution_after_arrival_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN LastExecution_last_execution_monotonic_correspondence". exact Logic.I. Qed.
Print Assumptions LastExecution_last_execution_monotonic_correspondence.
Goal Logic.True. idtac "AUDIT_END LastExecution_last_execution_monotonic_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN LastExecution_last_execution_idempotent_correspondence". exact Logic.I. Qed.
Print Assumptions LastExecution_last_execution_idempotent_correspondence.
Goal Logic.True. idtac "AUDIT_END LastExecution_last_execution_idempotent_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN LastExecution_last_execution_bounded_by_identity_correspondence". exact Logic.I. Qed.
Print Assumptions LastExecution_last_execution_bounded_by_identity_correspondence.
Goal Logic.True. idtac "AUDIT_END LastExecution_last_execution_bounded_by_identity_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN LastExecution_same_service_implies_same_last_execution_correspondence". exact Logic.I. Qed.
Print Assumptions LastExecution_same_service_implies_same_last_execution_correspondence.
Goal Logic.True. idtac "AUDIT_END LastExecution_same_service_implies_same_last_execution_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN LastExecution_same_service_since_last_execution_correspondence". exact Logic.I. Qed.
Print Assumptions LastExecution_same_service_since_last_execution_correspondence.
Goal Logic.True. idtac "AUDIT_END LastExecution_same_service_since_last_execution_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN LastExecution_exists_last_execution_with_smaller_service_correspondence". exact Logic.I. Qed.
Print Assumptions LastExecution_exists_last_execution_with_smaller_service_correspondence.
Goal Logic.True. idtac "AUDIT_END LastExecution_exists_last_execution_with_smaller_service_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN LastExecution_less_service_before_start_of_suspension_correspondence". exact Logic.I. Qed.
Print Assumptions LastExecution_less_service_before_start_of_suspension_correspondence.
Goal Logic.True. idtac "AUDIT_END LastExecution_less_service_before_start_of_suspension_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cle_forall_sched". exact Logic.I. Qed.
Print Assumptions cle_forall_sched.
Goal Logic.True. idtac "AUDIT_END cle_forall_sched". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cle_forall_par". exact Logic.I. Qed.
Print Assumptions cle_forall_par.
Goal Logic.True. idtac "AUDIT_END cle_forall_par". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cle_ico". exact Logic.I. Qed.
Print Assumptions cle_ico.
Goal Logic.True. idtac "AUDIT_END cle_ico". exact Logic.I. Qed.
