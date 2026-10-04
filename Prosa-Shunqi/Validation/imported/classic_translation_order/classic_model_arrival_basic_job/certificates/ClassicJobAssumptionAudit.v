From FoundationCertificates Require Import ClassicJobCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN Job_job_cost_positive_correspondence". exact Logic.I. Qed.
Print Assumptions Job_job_cost_positive_correspondence.
Goal Logic.True. idtac "AUDIT_END Job_job_cost_positive_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Job_job_deadline_positive_correspondence". exact Logic.I. Qed.
Print Assumptions Job_job_deadline_positive_correspondence.
Goal Logic.True. idtac "AUDIT_END Job_job_deadline_positive_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Job_job_cost_le_deadline_correspondence". exact Logic.I. Qed.
Print Assumptions Job_job_cost_le_deadline_correspondence.
Goal Logic.True. idtac "AUDIT_END Job_job_cost_le_deadline_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Job_valid_realtime_job_correspondence". exact Logic.I. Qed.
Print Assumptions Job_valid_realtime_job_correspondence.
Goal Logic.True. idtac "AUDIT_END Job_valid_realtime_job_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Job_job_cost_le_task_cost_correspondence". exact Logic.I. Qed.
Print Assumptions Job_job_cost_le_task_cost_correspondence.
Goal Logic.True. idtac "AUDIT_END Job_job_cost_le_task_cost_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Job_job_deadline_eq_task_deadline_correspondence". exact Logic.I. Qed.
Print Assumptions Job_job_deadline_eq_task_deadline_correspondence.
Goal Logic.True. idtac "AUDIT_END Job_job_deadline_eq_task_deadline_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Job_valid_sporadic_job_correspondence". exact Logic.I. Qed.
Print Assumptions Job_valid_sporadic_job_correspondence.
Goal Logic.True. idtac "AUDIT_END Job_valid_sporadic_job_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Job_cost_of_jobs_from_arrival_sequence_le_task_cost_correspondence". exact Logic.I. Qed.
Print Assumptions Job_cost_of_jobs_from_arrival_sequence_le_task_cost_correspondence.
Goal Logic.True. idtac "AUDIT_END Job_cost_of_jobs_from_arrival_sequence_le_task_cost_correspondence". exact Logic.I. Qed.
