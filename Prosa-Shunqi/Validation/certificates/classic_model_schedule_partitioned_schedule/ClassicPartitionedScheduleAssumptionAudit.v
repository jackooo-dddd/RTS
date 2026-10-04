From FoundationCertificates Require Import ClassicPartitionedScheduleCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN Partitioned_never_migrates_correspondence". exact Logic.I. Qed.
Print Assumptions Partitioned_never_migrates_correspondence.
Goal Logic.True. idtac "AUDIT_END Partitioned_never_migrates_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Partitioned_job_local_to_processor_correspondence". exact Logic.I. Qed.
Print Assumptions Partitioned_job_local_to_processor_correspondence.
Goal Logic.True. idtac "AUDIT_END Partitioned_job_local_to_processor_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Partitioned_task_local_to_processor_correspondence". exact Logic.I. Qed.
Print Assumptions Partitioned_task_local_to_processor_correspondence.
Goal Logic.True. idtac "AUDIT_END Partitioned_task_local_to_processor_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Partitioned_partitioned_schedule_correspondence". exact Logic.I. Qed.
Print Assumptions Partitioned_partitioned_schedule_correspondence.
Goal Logic.True. idtac "AUDIT_END Partitioned_partitioned_schedule_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Partitioned_local_jobs_dont_migrate_correspondence". exact Logic.I. Qed.
Print Assumptions Partitioned_local_jobs_dont_migrate_correspondence.
Goal Logic.True. idtac "AUDIT_END Partitioned_local_jobs_dont_migrate_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cps_forall_sched". exact Logic.I. Qed.
Print Assumptions cps_forall_sched.
Goal Logic.True. idtac "AUDIT_END cps_forall_sched". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cps_forall_ncpus_sched". exact Logic.I. Qed.
Print Assumptions cps_forall_ncpus_sched.
Goal Logic.True. idtac "AUDIT_END cps_forall_ncpus_sched". exact Logic.I. Qed.
