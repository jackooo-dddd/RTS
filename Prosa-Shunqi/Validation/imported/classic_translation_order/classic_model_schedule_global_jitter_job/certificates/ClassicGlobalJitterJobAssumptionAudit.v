From FoundationCertificates Require Import ClassicGlobalJitterJobCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN JobWithJitter_job_jitter_leq_task_jitter_correspondence". exact Logic.I. Qed.
Print Assumptions JobWithJitter_job_jitter_leq_task_jitter_correspondence.
Goal Logic.True. idtac "AUDIT_END JobWithJitter_job_jitter_leq_task_jitter_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN JobWithJitter_valid_sporadic_job_with_jitter_correspondence". exact Logic.I. Qed.
Print Assumptions JobWithJitter_valid_sporadic_job_with_jitter_correspondence.
Goal Logic.True. idtac "AUDIT_END JobWithJitter_valid_sporadic_job_with_jitter_correspondence". exact Logic.I. Qed.
