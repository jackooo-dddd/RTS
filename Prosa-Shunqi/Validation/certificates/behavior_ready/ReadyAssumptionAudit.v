From FoundationCertificates Require Import ReadyCorrespondence.

Goal True. idtac "AUDIT_BEGIN JobReady". exact I. Qed.
Print Assumptions job_ready_class_correspondence.
Goal True. idtac "AUDIT_END JobReady". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN backlogged". exact I. Qed.
Print Assumptions backlogged_correspondence.
Goal True. idtac "AUDIT_END backlogged". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN jobs_come_from_arrival_sequence". exact I. Qed.
Print Assumptions jobs_come_from_arrival_sequence_correspondence.
Goal True. idtac "AUDIT_END jobs_come_from_arrival_sequence". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN jobs_must_arrive_to_execute". exact I. Qed.
Print Assumptions jobs_must_arrive_to_execute_correspondence.
Goal True. idtac "AUDIT_END jobs_must_arrive_to_execute". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN jobs_must_be_ready_to_execute". exact I. Qed.
Print Assumptions jobs_must_be_ready_to_execute_correspondence.
Goal True. idtac "AUDIT_END jobs_must_be_ready_to_execute". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN completed_jobs_dont_execute". exact I. Qed.
Print Assumptions completed_jobs_dont_execute_correspondence.
Goal True. idtac "AUDIT_END completed_jobs_dont_execute". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN valid_schedule". exact I. Qed.
Print Assumptions valid_schedule_correspondence.
Goal True. idtac "AUDIT_END valid_schedule". exact I. Qed.
