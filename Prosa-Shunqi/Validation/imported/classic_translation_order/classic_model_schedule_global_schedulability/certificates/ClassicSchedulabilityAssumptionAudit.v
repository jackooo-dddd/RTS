From FoundationCertificates Require Import ClassicSchedulabilityCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN Schedulability_job_misses_no_deadline_correspondence". exact Logic.I. Qed.
Print Assumptions Schedulability_job_misses_no_deadline_correspondence.
Goal Logic.True. idtac "AUDIT_END Schedulability_job_misses_no_deadline_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Schedulability_task_misses_no_deadline_correspondence". exact Logic.I. Qed.
Print Assumptions Schedulability_task_misses_no_deadline_correspondence.
Goal Logic.True. idtac "AUDIT_END Schedulability_task_misses_no_deadline_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Schedulability_task_misses_no_deadline_before_correspondence". exact Logic.I. Qed.
Print Assumptions Schedulability_task_misses_no_deadline_before_correspondence.
Goal Logic.True. idtac "AUDIT_END Schedulability_task_misses_no_deadline_before_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Schedulability_service_after_job_deadline_zero_correspondence". exact Logic.I. Qed.
Print Assumptions Schedulability_service_after_job_deadline_zero_correspondence.
Goal Logic.True. idtac "AUDIT_END Schedulability_service_after_job_deadline_zero_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Schedulability_cumulative_service_after_job_deadline_zero_correspondence". exact Logic.I. Qed.
Print Assumptions Schedulability_cumulative_service_after_job_deadline_zero_correspondence.
Goal Logic.True. idtac "AUDIT_END Schedulability_cumulative_service_after_job_deadline_zero_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Schedulability_service_after_task_deadline_zero_correspondence". exact Logic.I. Qed.
Print Assumptions Schedulability_service_after_task_deadline_zero_correspondence.
Goal Logic.True. idtac "AUDIT_END Schedulability_service_after_task_deadline_zero_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Schedulability_cumulative_service_after_task_deadline_zero_correspondence". exact Logic.I. Qed.
Print Assumptions Schedulability_cumulative_service_after_task_deadline_zero_correspondence.
Goal Logic.True. idtac "AUDIT_END Schedulability_cumulative_service_after_task_deadline_zero_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cs_forall_ncpus_sched". exact Logic.I. Qed.
Print Assumptions cs_forall_ncpus_sched.
Goal Logic.True. idtac "AUDIT_END cs_forall_ncpus_sched". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cs_ico". exact Logic.I. Qed.
Print Assumptions cs_ico.
Goal Logic.True. idtac "AUDIT_END cs_ico". exact Logic.I. Qed.
