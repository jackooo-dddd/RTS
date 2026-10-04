From FoundationCertificates Require Import ClassicGlobalJitterScheduleCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN ScheduleWithJitter_actual_arrival_correspondence". exact Logic.I. Qed.
Print Assumptions ScheduleWithJitter_actual_arrival_correspondence.
Goal Logic.True. idtac "AUDIT_END ScheduleWithJitter_actual_arrival_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ScheduleWithJitter_jitter_has_passed_correspondence". exact Logic.I. Qed.
Print Assumptions ScheduleWithJitter_jitter_has_passed_correspondence.
Goal Logic.True. idtac "AUDIT_END ScheduleWithJitter_jitter_has_passed_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ScheduleWithJitter_actual_arrival_before_correspondence". exact Logic.I. Qed.
Print Assumptions ScheduleWithJitter_actual_arrival_before_correspondence.
Goal Logic.True. idtac "AUDIT_END ScheduleWithJitter_actual_arrival_before_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ScheduleWithJitter_pending_correspondence". exact Logic.I. Qed.
Print Assumptions ScheduleWithJitter_pending_correspondence.
Goal Logic.True. idtac "AUDIT_END ScheduleWithJitter_pending_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ScheduleWithJitter_backlogged_correspondence". exact Logic.I. Qed.
Print Assumptions ScheduleWithJitter_backlogged_correspondence.
Goal Logic.True. idtac "AUDIT_END ScheduleWithJitter_backlogged_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ScheduleWithJitter_jobs_execute_after_jitter_correspondence". exact Logic.I. Qed.
Print Assumptions ScheduleWithJitter_jobs_execute_after_jitter_correspondence.
Goal Logic.True. idtac "AUDIT_END ScheduleWithJitter_jobs_execute_after_jitter_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ScheduleWithJitter_scheduled_implies_pending_correspondence". exact Logic.I. Qed.
Print Assumptions ScheduleWithJitter_scheduled_implies_pending_correspondence.
Goal Logic.True. idtac "AUDIT_END ScheduleWithJitter_scheduled_implies_pending_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ScheduleWithJitter_arrival_before_jitter_correspondence". exact Logic.I. Qed.
Print Assumptions ScheduleWithJitter_arrival_before_jitter_correspondence.
Goal Logic.True. idtac "AUDIT_END ScheduleWithJitter_arrival_before_jitter_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ScheduleWithJitter_service_before_jitter_zero_correspondence". exact Logic.I. Qed.
Print Assumptions ScheduleWithJitter_service_before_jitter_zero_correspondence.
Goal Logic.True. idtac "AUDIT_END ScheduleWithJitter_service_before_jitter_zero_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ScheduleWithJitter_cumulative_service_before_jitter_zero_correspondence". exact Logic.I. Qed.
Print Assumptions ScheduleWithJitter_cumulative_service_before_jitter_zero_correspondence.
Goal Logic.True. idtac "AUDIT_END ScheduleWithJitter_cumulative_service_before_jitter_zero_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ScheduleOfSporadicTaskWithJitter_task_scheduled_on_correspondence". exact Logic.I. Qed.
Print Assumptions ScheduleOfSporadicTaskWithJitter_task_scheduled_on_correspondence.
Goal Logic.True. idtac "AUDIT_END ScheduleOfSporadicTaskWithJitter_task_scheduled_on_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ScheduleOfSporadicTaskWithJitter_task_is_scheduled_correspondence". exact Logic.I. Qed.
Print Assumptions ScheduleOfSporadicTaskWithJitter_task_is_scheduled_correspondence.
Goal Logic.True. idtac "AUDIT_END ScheduleOfSporadicTaskWithJitter_task_is_scheduled_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ScheduleOfSporadicTaskWithJitter_jobs_of_task_scheduled_between_correspondence". exact Logic.I. Qed.
Print Assumptions ScheduleOfSporadicTaskWithJitter_jobs_of_task_scheduled_between_correspondence.
Goal Logic.True. idtac "AUDIT_END ScheduleOfSporadicTaskWithJitter_jobs_of_task_scheduled_between_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ScheduleOfSporadicTaskWithJitter_jobs_of_same_task_dont_execute_in_parallel_correspondence". exact Logic.I. Qed.
Print Assumptions ScheduleOfSporadicTaskWithJitter_jobs_of_same_task_dont_execute_in_parallel_correspondence.
Goal Logic.True. idtac "AUDIT_END ScheduleOfSporadicTaskWithJitter_jobs_of_same_task_dont_execute_in_parallel_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ScheduleOfSporadicTaskWithJitter_cumulative_service_le_task_cost_correspondence". exact Logic.I. Qed.
Print Assumptions ScheduleOfSporadicTaskWithJitter_cumulative_service_le_task_cost_correspondence.
Goal Logic.True. idtac "AUDIT_END ScheduleOfSporadicTaskWithJitter_cumulative_service_le_task_cost_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cgj_forall_sched". exact Logic.I. Qed.
Print Assumptions cgj_forall_sched.
Goal Logic.True. idtac "AUDIT_END cgj_forall_sched". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cgj_forall_ncpus_sched". exact Logic.I. Qed.
Print Assumptions cgj_forall_ncpus_sched.
Goal Logic.True. idtac "AUDIT_END cgj_forall_ncpus_sched". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cgj_ico". exact Logic.I. Qed.
Print Assumptions cgj_ico.
Goal Logic.True. idtac "AUDIT_END cgj_ico". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cgj_bigcat_nat_rel". exact Logic.I. Qed.
Print Assumptions cgj_bigcat_nat_rel.
Goal Logic.True. idtac "AUDIT_END cgj_bigcat_nat_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cgj_undup_rel". exact Logic.I. Qed.
Print Assumptions cgj_undup_rel.
Goal Logic.True. idtac "AUDIT_END cgj_undup_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cgj_forall_par". exact Logic.I. Qed.
Print Assumptions cgj_forall_par.
Goal Logic.True. idtac "AUDIT_END cgj_forall_par". exact Logic.I. Qed.
