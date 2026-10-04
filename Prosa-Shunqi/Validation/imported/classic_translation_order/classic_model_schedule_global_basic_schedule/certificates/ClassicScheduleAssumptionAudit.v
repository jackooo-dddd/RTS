From FoundationCertificates Require Import ClassicScheduleCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN Schedule_processor_correspondence". exact Logic.I. Qed.
Print Assumptions Schedule_processor_correspondence.
Goal Logic.True. idtac "AUDIT_END Schedule_processor_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Schedule_schedule_correspondence". exact Logic.I. Qed.
Print Assumptions Schedule_schedule_correspondence.
Goal Logic.True. idtac "AUDIT_END Schedule_schedule_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Schedule_scheduled_on_correspondence". exact Logic.I. Qed.
Print Assumptions Schedule_scheduled_on_correspondence.
Goal Logic.True. idtac "AUDIT_END Schedule_scheduled_on_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Schedule_scheduled_correspondence". exact Logic.I. Qed.
Print Assumptions Schedule_scheduled_correspondence.
Goal Logic.True. idtac "AUDIT_END Schedule_scheduled_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Schedule_is_idle_correspondence". exact Logic.I. Qed.
Print Assumptions Schedule_is_idle_correspondence.
Goal Logic.True. idtac "AUDIT_END Schedule_is_idle_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Schedule_service_at_correspondence". exact Logic.I. Qed.
Print Assumptions Schedule_service_at_correspondence.
Goal Logic.True. idtac "AUDIT_END Schedule_service_at_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Schedule_service_correspondence". exact Logic.I. Qed.
Print Assumptions Schedule_service_correspondence.
Goal Logic.True. idtac "AUDIT_END Schedule_service_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Schedule_service_during_correspondence". exact Logic.I. Qed.
Print Assumptions Schedule_service_during_correspondence.
Goal Logic.True. idtac "AUDIT_END Schedule_service_during_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Schedule_completed_correspondence". exact Logic.I. Qed.
Print Assumptions Schedule_completed_correspondence.
Goal Logic.True. idtac "AUDIT_END Schedule_completed_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Schedule_pending_correspondence". exact Logic.I. Qed.
Print Assumptions Schedule_pending_correspondence.
Goal Logic.True. idtac "AUDIT_END Schedule_pending_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Schedule_backlogged_correspondence". exact Logic.I. Qed.
Print Assumptions Schedule_backlogged_correspondence.
Goal Logic.True. idtac "AUDIT_END Schedule_backlogged_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Schedule_carried_in_correspondence". exact Logic.I. Qed.
Print Assumptions Schedule_carried_in_correspondence.
Goal Logic.True. idtac "AUDIT_END Schedule_carried_in_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Schedule_carried_out_correspondence". exact Logic.I. Qed.
Print Assumptions Schedule_carried_out_correspondence.
Goal Logic.True. idtac "AUDIT_END Schedule_carried_out_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Schedule_jobs_scheduled_at_correspondence". exact Logic.I. Qed.
Print Assumptions Schedule_jobs_scheduled_at_correspondence.
Goal Logic.True. idtac "AUDIT_END Schedule_jobs_scheduled_at_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Schedule_jobs_scheduled_between_correspondence". exact Logic.I. Qed.
Print Assumptions Schedule_jobs_scheduled_between_correspondence.
Goal Logic.True. idtac "AUDIT_END Schedule_jobs_scheduled_between_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Schedule_sequential_jobs_correspondence". exact Logic.I. Qed.
Print Assumptions Schedule_sequential_jobs_correspondence.
Goal Logic.True. idtac "AUDIT_END Schedule_sequential_jobs_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Schedule_jobs_must_arrive_to_execute_correspondence". exact Logic.I. Qed.
Print Assumptions Schedule_jobs_must_arrive_to_execute_correspondence.
Goal Logic.True. idtac "AUDIT_END Schedule_jobs_must_arrive_to_execute_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Schedule_completed_jobs_dont_execute_correspondence". exact Logic.I. Qed.
Print Assumptions Schedule_completed_jobs_dont_execute_correspondence.
Goal Logic.True. idtac "AUDIT_END Schedule_completed_jobs_dont_execute_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Schedule_jobs_come_from_arrival_sequence_correspondence". exact Logic.I. Qed.
Print Assumptions Schedule_jobs_come_from_arrival_sequence_correspondence.
Goal Logic.True. idtac "AUDIT_END Schedule_jobs_come_from_arrival_sequence_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Schedule_not_scheduled_no_service_correspondence". exact Logic.I. Qed.
Print Assumptions Schedule_not_scheduled_no_service_correspondence.
Goal Logic.True. idtac "AUDIT_END Schedule_not_scheduled_no_service_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Schedule_cumulative_service_implies_service_correspondence". exact Logic.I. Qed.
Print Assumptions Schedule_cumulative_service_implies_service_correspondence.
Goal Logic.True. idtac "AUDIT_END Schedule_cumulative_service_implies_service_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Schedule_service_implies_cumulative_service_correspondence". exact Logic.I. Qed.
Print Assumptions Schedule_service_implies_cumulative_service_correspondence.
Goal Logic.True. idtac "AUDIT_END Schedule_service_implies_cumulative_service_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Schedule_service_at_most_one_correspondence". exact Logic.I. Qed.
Print Assumptions Schedule_service_at_most_one_correspondence.
Goal Logic.True. idtac "AUDIT_END Schedule_service_at_most_one_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Schedule_cumulative_service_le_delta_correspondence". exact Logic.I. Qed.
Print Assumptions Schedule_cumulative_service_le_delta_correspondence.
Goal Logic.True. idtac "AUDIT_END Schedule_cumulative_service_le_delta_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Schedule_completion_monotonic_correspondence". exact Logic.I. Qed.
Print Assumptions Schedule_completion_monotonic_correspondence.
Goal Logic.True. idtac "AUDIT_END Schedule_completion_monotonic_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Schedule_completed_implies_not_scheduled_correspondence". exact Logic.I. Qed.
Print Assumptions Schedule_completed_implies_not_scheduled_correspondence.
Goal Logic.True. idtac "AUDIT_END Schedule_completed_implies_not_scheduled_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Schedule_cumulative_service_le_job_cost_correspondence". exact Logic.I. Qed.
Print Assumptions Schedule_cumulative_service_le_job_cost_correspondence.
Goal Logic.True. idtac "AUDIT_END Schedule_cumulative_service_le_job_cost_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Schedule_service_before_job_arrival_zero_correspondence". exact Logic.I. Qed.
Print Assumptions Schedule_service_before_job_arrival_zero_correspondence.
Goal Logic.True. idtac "AUDIT_END Schedule_service_before_job_arrival_zero_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Schedule_cumulative_service_before_job_arrival_zero_correspondence". exact Logic.I. Qed.
Print Assumptions Schedule_cumulative_service_before_job_arrival_zero_correspondence.
Goal Logic.True. idtac "AUDIT_END Schedule_cumulative_service_before_job_arrival_zero_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Schedule_service_before_arrival_eq_service_during_correspondence". exact Logic.I. Qed.
Print Assumptions Schedule_service_before_arrival_eq_service_during_correspondence.
Goal Logic.True. idtac "AUDIT_END Schedule_service_before_arrival_eq_service_during_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Schedule_scheduled_implies_pending_correspondence". exact Logic.I. Qed.
Print Assumptions Schedule_scheduled_implies_pending_correspondence.
Goal Logic.True. idtac "AUDIT_END Schedule_scheduled_implies_pending_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Schedule_mem_scheduled_jobs_eq_scheduled_correspondence". exact Logic.I. Qed.
Print Assumptions Schedule_mem_scheduled_jobs_eq_scheduled_correspondence.
Goal Logic.True. idtac "AUDIT_END Schedule_mem_scheduled_jobs_eq_scheduled_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Schedule_scheduled_jobs_uniq_correspondence". exact Logic.I. Qed.
Print Assumptions Schedule_scheduled_jobs_uniq_correspondence.
Goal Logic.True. idtac "AUDIT_END Schedule_scheduled_jobs_uniq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Schedule_num_scheduled_jobs_le_num_cpus_correspondence". exact Logic.I. Qed.
Print Assumptions Schedule_num_scheduled_jobs_le_num_cpus_correspondence.
Goal Logic.True. idtac "AUDIT_END Schedule_num_scheduled_jobs_le_num_cpus_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ScheduleOfSporadicTask_task_scheduled_on_correspondence". exact Logic.I. Qed.
Print Assumptions ScheduleOfSporadicTask_task_scheduled_on_correspondence.
Goal Logic.True. idtac "AUDIT_END ScheduleOfSporadicTask_task_scheduled_on_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ScheduleOfSporadicTask_task_is_scheduled_correspondence". exact Logic.I. Qed.
Print Assumptions ScheduleOfSporadicTask_task_is_scheduled_correspondence.
Goal Logic.True. idtac "AUDIT_END ScheduleOfSporadicTask_task_is_scheduled_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ScheduleOfSporadicTask_jobs_of_task_scheduled_between_correspondence". exact Logic.I. Qed.
Print Assumptions ScheduleOfSporadicTask_jobs_of_task_scheduled_between_correspondence.
Goal Logic.True. idtac "AUDIT_END ScheduleOfSporadicTask_jobs_of_task_scheduled_between_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ScheduleOfSporadicTask_jobs_of_same_task_dont_execute_in_parallel_correspondence". exact Logic.I. Qed.
Print Assumptions ScheduleOfSporadicTask_jobs_of_same_task_dont_execute_in_parallel_correspondence.
Goal Logic.True. idtac "AUDIT_END ScheduleOfSporadicTask_jobs_of_same_task_dont_execute_in_parallel_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ScheduleOfSporadicTask_cumulative_service_le_task_cost_correspondence". exact Logic.I. Qed.
Print Assumptions ScheduleOfSporadicTask_cumulative_service_le_task_cost_correspondence.
Goal Logic.True. idtac "AUDIT_END ScheduleOfSporadicTask_cumulative_service_le_task_cost_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cs_forall_sched". exact Logic.I. Qed.
Print Assumptions cs_forall_sched.
Goal Logic.True. idtac "AUDIT_END cs_forall_sched". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cs_forall_ncpus_sched". exact Logic.I. Qed.
Print Assumptions cs_forall_ncpus_sched.
Goal Logic.True. idtac "AUDIT_END cs_forall_ncpus_sched". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cs_ico". exact Logic.I. Qed.
Print Assumptions cs_ico.
Goal Logic.True. idtac "AUDIT_END cs_ico". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cs_bigcat_nat_rel". exact Logic.I. Qed.
Print Assumptions cs_bigcat_nat_rel.
Goal Logic.True. idtac "AUDIT_END cs_bigcat_nat_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cs_undup_rel". exact Logic.I. Qed.
Print Assumptions cs_undup_rel.
Goal Logic.True. idtac "AUDIT_END cs_undup_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cs_forall_par". exact Logic.I. Qed.
Print Assumptions cs_forall_par.
Goal Logic.True. idtac "AUDIT_END cs_forall_par". exact Logic.I. Qed.
