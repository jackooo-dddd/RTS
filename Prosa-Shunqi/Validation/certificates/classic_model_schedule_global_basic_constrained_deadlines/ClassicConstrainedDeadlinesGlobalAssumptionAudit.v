From FoundationCertificates Require Import ClassicConstrainedDeadlinesGlobalCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN ConstrainedDeadlines_platform_at_most_one_pending_job_of_each_task_correspondence". exact Logic.I. Qed.
Print Assumptions ConstrainedDeadlines_platform_at_most_one_pending_job_of_each_task_correspondence.
Goal Logic.True. idtac "AUDIT_END ConstrainedDeadlines_platform_at_most_one_pending_job_of_each_task_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ConstrainedDeadlines_platform_cpus_busy_with_interfering_tasks_correspondence". exact Logic.I. Qed.
Print Assumptions ConstrainedDeadlines_platform_cpus_busy_with_interfering_tasks_correspondence.
Goal Logic.True. idtac "AUDIT_END ConstrainedDeadlines_platform_cpus_busy_with_interfering_tasks_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ConstrainedDeadlines_scheduled_task_with_higher_eq_priority_correspondence". exact Logic.I. Qed.
Print Assumptions ConstrainedDeadlines_scheduled_task_with_higher_eq_priority_correspondence.
Goal Logic.True. idtac "AUDIT_END ConstrainedDeadlines_scheduled_task_with_higher_eq_priority_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ConstrainedDeadlines_platform_fp_no_multiple_jobs_of_interfering_tasks_correspondence". exact Logic.I. Qed.
Print Assumptions ConstrainedDeadlines_platform_fp_no_multiple_jobs_of_interfering_tasks_correspondence.
Goal Logic.True. idtac "AUDIT_END ConstrainedDeadlines_platform_fp_no_multiple_jobs_of_interfering_tasks_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ConstrainedDeadlines_platform_fp_no_multiple_jobs_of_tsk_correspondence". exact Logic.I. Qed.
Print Assumptions ConstrainedDeadlines_platform_fp_no_multiple_jobs_of_tsk_correspondence.
Goal Logic.True. idtac "AUDIT_END ConstrainedDeadlines_platform_fp_no_multiple_jobs_of_tsk_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ConstrainedDeadlines_platform_fp_cpus_busy_with_interfering_tasks_correspondence". exact Logic.I. Qed.
Print Assumptions ConstrainedDeadlines_platform_fp_cpus_busy_with_interfering_tasks_correspondence.
Goal Logic.True. idtac "AUDIT_END ConstrainedDeadlines_platform_fp_cpus_busy_with_interfering_tasks_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cs_forall_ncpus_sched". exact Logic.I. Qed.
Print Assumptions cs_forall_ncpus_sched.
Goal Logic.True. idtac "AUDIT_END cs_forall_ncpus_sched". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cs_forall_sched". exact Logic.I. Qed.
Print Assumptions cs_forall_sched.
Goal Logic.True. idtac "AUDIT_END cs_forall_sched". exact Logic.I. Qed.
