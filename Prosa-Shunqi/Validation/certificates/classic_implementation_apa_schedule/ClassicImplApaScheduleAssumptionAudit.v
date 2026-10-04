From FoundationCertificates Require Import ClassicImplApaScheduleCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN ConcreteScheduler_pending_jobs_correspondence". exact Logic.I. Qed.
Print Assumptions ConcreteScheduler_pending_jobs_correspondence.
Goal Logic.True. idtac "AUDIT_END ConcreteScheduler_pending_jobs_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ConcreteScheduler_sorted_pending_jobs_correspondence". exact Logic.I. Qed.
Print Assumptions ConcreteScheduler_sorted_pending_jobs_correspondence.
Goal Logic.True. idtac "AUDIT_END ConcreteScheduler_sorted_pending_jobs_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ConcreteScheduler_should_be_scheduled_correspondence". exact Logic.I. Qed.
Print Assumptions ConcreteScheduler_should_be_scheduled_correspondence.
Goal Logic.True. idtac "AUDIT_END ConcreteScheduler_should_be_scheduled_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ConcreteScheduler_update_available_cpu_correspondence". exact Logic.I. Qed.
Print Assumptions ConcreteScheduler_update_available_cpu_correspondence.
Goal Logic.True. idtac "AUDIT_END ConcreteScheduler_update_available_cpu_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ConcreteScheduler_schedule_jobs_from_list_correspondence". exact Logic.I. Qed.
Print Assumptions ConcreteScheduler_schedule_jobs_from_list_correspondence.
Goal Logic.True. idtac "AUDIT_END ConcreteScheduler_schedule_jobs_from_list_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ConcreteScheduler_apa_schedule_correspondence". exact Logic.I. Qed.
Print Assumptions ConcreteScheduler_apa_schedule_correspondence.
Goal Logic.True. idtac "AUDIT_END ConcreteScheduler_apa_schedule_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ConcreteScheduler_scheduler_correspondence". exact Logic.I. Qed.
Print Assumptions ConcreteScheduler_scheduler_correspondence.
Goal Logic.True. idtac "AUDIT_END ConcreteScheduler_scheduler_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ConcreteScheduler_scheduler_depends_only_on_prefix_correspondence". exact Logic.I. Qed.
Print Assumptions ConcreteScheduler_scheduler_depends_only_on_prefix_correspondence.
Goal Logic.True. idtac "AUDIT_END ConcreteScheduler_scheduler_depends_only_on_prefix_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ConcreteScheduler_scheduler_uses_construction_function_correspondence". exact Logic.I. Qed.
Print Assumptions ConcreteScheduler_scheduler_uses_construction_function_correspondence.
Goal Logic.True. idtac "AUDIT_END ConcreteScheduler_scheduler_uses_construction_function_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ConcreteScheduler_scheduler_uniq_cpus_correspondence". exact Logic.I. Qed.
Print Assumptions ConcreteScheduler_scheduler_uniq_cpus_correspondence.
Goal Logic.True. idtac "AUDIT_END ConcreteScheduler_scheduler_uniq_cpus_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ConcreteScheduler_scheduler_job_in_mapping_correspondence". exact Logic.I. Qed.
Print Assumptions ConcreteScheduler_scheduler_job_in_mapping_correspondence.
Goal Logic.True. idtac "AUDIT_END ConcreteScheduler_scheduler_job_in_mapping_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ConcreteScheduler_scheduler_mapping_respects_affinity_correspondence". exact Logic.I. Qed.
Print Assumptions ConcreteScheduler_scheduler_mapping_respects_affinity_correspondence.
Goal Logic.True. idtac "AUDIT_END ConcreteScheduler_scheduler_mapping_respects_affinity_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ConcreteScheduler_scheduler_has_no_duplicate_jobs_correspondence". exact Logic.I. Qed.
Print Assumptions ConcreteScheduler_scheduler_has_no_duplicate_jobs_correspondence.
Goal Logic.True. idtac "AUDIT_END ConcreteScheduler_scheduler_has_no_duplicate_jobs_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ConcreteScheduler_scheduler_scheduled_on_correspondence". exact Logic.I. Qed.
Print Assumptions ConcreteScheduler_scheduler_scheduled_on_correspondence.
Goal Logic.True. idtac "AUDIT_END ConcreteScheduler_scheduler_scheduled_on_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ConcreteScheduler_scheduler_has_cpus_correspondence". exact Logic.I. Qed.
Print Assumptions ConcreteScheduler_scheduler_has_cpus_correspondence.
Goal Logic.True. idtac "AUDIT_END ConcreteScheduler_scheduler_has_cpus_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ConcreteScheduler_scheduler_mapping_is_work_conserving_correspondence". exact Logic.I. Qed.
Print Assumptions ConcreteScheduler_scheduler_mapping_is_work_conserving_correspondence.
Goal Logic.True. idtac "AUDIT_END ConcreteScheduler_scheduler_mapping_is_work_conserving_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ConcreteScheduler_scheduler_priority_correspondence". exact Logic.I. Qed.
Print Assumptions ConcreteScheduler_scheduler_priority_correspondence.
Goal Logic.True. idtac "AUDIT_END ConcreteScheduler_scheduler_priority_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ConcreteScheduler_scheduler_jobs_come_from_arrival_sequence_correspondence". exact Logic.I. Qed.
Print Assumptions ConcreteScheduler_scheduler_jobs_come_from_arrival_sequence_correspondence.
Goal Logic.True. idtac "AUDIT_END ConcreteScheduler_scheduler_jobs_come_from_arrival_sequence_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ConcreteScheduler_scheduler_jobs_must_arrive_to_execute_correspondence". exact Logic.I. Qed.
Print Assumptions ConcreteScheduler_scheduler_jobs_must_arrive_to_execute_correspondence.
Goal Logic.True. idtac "AUDIT_END ConcreteScheduler_scheduler_jobs_must_arrive_to_execute_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ConcreteScheduler_scheduler_sequential_jobs_correspondence". exact Logic.I. Qed.
Print Assumptions ConcreteScheduler_scheduler_sequential_jobs_correspondence.
Goal Logic.True. idtac "AUDIT_END ConcreteScheduler_scheduler_sequential_jobs_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ConcreteScheduler_scheduler_completed_jobs_dont_execute_correspondence". exact Logic.I. Qed.
Print Assumptions ConcreteScheduler_scheduler_completed_jobs_dont_execute_correspondence.
Goal Logic.True. idtac "AUDIT_END ConcreteScheduler_scheduler_completed_jobs_dont_execute_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ConcreteScheduler_scheduler_apa_work_conserving_correspondence". exact Logic.I. Qed.
Print Assumptions ConcreteScheduler_scheduler_apa_work_conserving_correspondence.
Goal Logic.True. idtac "AUDIT_END ConcreteScheduler_scheduler_apa_work_conserving_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ConcreteScheduler_scheduler_respects_affinity_correspondence". exact Logic.I. Qed.
Print Assumptions ConcreteScheduler_scheduler_respects_affinity_correspondence.
Goal Logic.True. idtac "AUDIT_END ConcreteScheduler_scheduler_respects_affinity_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ConcreteScheduler_scheduler_respects_policy_correspondence". exact Logic.I. Qed.
Print Assumptions ConcreteScheduler_scheduler_respects_policy_correspondence.
Goal Logic.True. idtac "AUDIT_END ConcreteScheduler_scheduler_respects_policy_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cs_forall_sched". exact Logic.I. Qed.
Print Assumptions cs_forall_sched.
Goal Logic.True. idtac "AUDIT_END cs_forall_sched". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cs_forall_jldp". exact Logic.I. Qed.
Print Assumptions cs_forall_jldp.
Goal Logic.True. idtac "AUDIT_END cs_forall_jldp". exact Logic.I. Qed.
