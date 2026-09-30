From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence CurvesCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations ProgressHelpers SuspensionCorrespondence DynamicSuspensionCorrespondence DsPStateCover FactsDynamicSuspensionCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN job_suspension_bounded_correspondence". exact Logic.I. Qed.
Print Assumptions job_suspension_bounded_correspondence.
Goal Logic.True. idtac "AUDIT_END job_suspension_bounded_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN suspension_of_task_bounded_correspondence". exact Logic.I. Qed.
Print Assumptions suspension_of_task_bounded_correspondence.
Goal Logic.True. idtac "AUDIT_END suspension_of_task_bounded_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fds_nat_of_bool_related". exact Logic.I. Qed.
Print Assumptions fds_nat_of_bool_related.
Goal Logic.True. idtac "AUDIT_END fds_nat_of_bool_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fds_valid_related". exact Logic.I. Qed.
Print Assumptions fds_valid_related.
Goal Logic.True. idtac "AUDIT_END fds_valid_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fds_suspended_related". exact Logic.I. Qed.
Print Assumptions fds_suspended_related.
Goal Logic.True. idtac "AUDIT_END fds_suspended_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fds_job_sum_related". exact Logic.I. Qed.
Print Assumptions fds_job_sum_related.
Goal Logic.True. idtac "AUDIT_END fds_job_sum_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fds_forall_cover". exact Logic.I. Qed.
Print Assumptions fds_forall_cover.
Goal Logic.True. idtac "AUDIT_END fds_forall_cover". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fds_nat_input". exact Logic.I. Qed.
Print Assumptions fds_nat_input.
Goal Logic.True. idtac "AUDIT_END fds_nat_input". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fds_forall_sched". exact Logic.I. Qed.
Print Assumptions fds_forall_sched.
Goal Logic.True. idtac "AUDIT_END fds_forall_sched". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fds_forall_arr". exact Logic.I. Qed.
Print Assumptions fds_forall_arr.
Goal Logic.True. idtac "AUDIT_END fds_forall_arr". exact Logic.I. Qed.
