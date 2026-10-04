From FoundationCertificates Require Import ClassicUniSchedulabilityCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN Schedulability_job_misses_no_deadline_correspondence". exact Logic.I. Qed.
Print Assumptions Schedulability_job_misses_no_deadline_correspondence.
Goal Logic.True. idtac "AUDIT_END Schedulability_job_misses_no_deadline_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Schedulability_task_misses_no_deadline_correspondence". exact Logic.I. Qed.
Print Assumptions Schedulability_task_misses_no_deadline_correspondence.
Goal Logic.True. idtac "AUDIT_END Schedulability_task_misses_no_deadline_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Schedulability_taskset_misses_no_deadline_correspondence". exact Logic.I. Qed.
Print Assumptions Schedulability_taskset_misses_no_deadline_correspondence.
Goal Logic.True. idtac "AUDIT_END Schedulability_taskset_misses_no_deadline_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Schedulability_task_completes_before_deadline_correspondence". exact Logic.I. Qed.
Print Assumptions Schedulability_task_completes_before_deadline_correspondence.
Goal Logic.True. idtac "AUDIT_END Schedulability_task_completes_before_deadline_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN csc_forall_sched". exact Logic.I. Qed.
Print Assumptions csc_forall_sched.
Goal Logic.True. idtac "AUDIT_END csc_forall_sched". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN csc_forall_par". exact Logic.I. Qed.
Print Assumptions csc_forall_par.
Goal Logic.True. idtac "AUDIT_END csc_forall_par". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN csc_ico". exact Logic.I. Qed.
Print Assumptions csc_ico.
Goal Logic.True. idtac "AUDIT_END csc_ico". exact Logic.I. Qed.
