From FoundationCertificates Require Import ClassicUniJitterScheduleCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN UniprocessorScheduleWithJitter_pending_correspondence". exact Logic.I. Qed.
Print Assumptions UniprocessorScheduleWithJitter_pending_correspondence.
Goal Logic.True. idtac "AUDIT_END UniprocessorScheduleWithJitter_pending_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN UniprocessorScheduleWithJitter_backlogged_correspondence". exact Logic.I. Qed.
Print Assumptions UniprocessorScheduleWithJitter_backlogged_correspondence.
Goal Logic.True. idtac "AUDIT_END UniprocessorScheduleWithJitter_backlogged_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN UniprocessorScheduleWithJitter_jobs_execute_after_jitter_correspondence". exact Logic.I. Qed.
Print Assumptions UniprocessorScheduleWithJitter_jobs_execute_after_jitter_correspondence.
Goal Logic.True. idtac "AUDIT_END UniprocessorScheduleWithJitter_jobs_execute_after_jitter_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN UniprocessorScheduleWithJitter_jobs_with_jitter_must_arrive_to_execute_correspondence". exact Logic.I. Qed.
Print Assumptions UniprocessorScheduleWithJitter_jobs_with_jitter_must_arrive_to_execute_correspondence.
Goal Logic.True. idtac "AUDIT_END UniprocessorScheduleWithJitter_jobs_with_jitter_must_arrive_to_execute_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN UniprocessorScheduleWithJitter_jitter_has_passed_implies_arrived_correspondence". exact Logic.I. Qed.
Print Assumptions UniprocessorScheduleWithJitter_jitter_has_passed_implies_arrived_correspondence.
Goal Logic.True. idtac "AUDIT_END UniprocessorScheduleWithJitter_jitter_has_passed_implies_arrived_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN UniprocessorScheduleWithJitter_service_before_jitter_is_zero_correspondence". exact Logic.I. Qed.
Print Assumptions UniprocessorScheduleWithJitter_service_before_jitter_is_zero_correspondence.
Goal Logic.True. idtac "AUDIT_END UniprocessorScheduleWithJitter_service_before_jitter_is_zero_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN UniprocessorScheduleWithJitter_cumulative_service_before_jitter_is_zero_correspondence". exact Logic.I. Qed.
Print Assumptions UniprocessorScheduleWithJitter_cumulative_service_before_jitter_is_zero_correspondence.
Goal Logic.True. idtac "AUDIT_END UniprocessorScheduleWithJitter_cumulative_service_before_jitter_is_zero_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN UniprocessorScheduleWithJitter_ignore_service_before_jitter_correspondence". exact Logic.I. Qed.
Print Assumptions UniprocessorScheduleWithJitter_ignore_service_before_jitter_correspondence.
Goal Logic.True. idtac "AUDIT_END UniprocessorScheduleWithJitter_ignore_service_before_jitter_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN UniprocessorScheduleWithJitter_scheduled_implies_pending_correspondence". exact Logic.I. Qed.
Print Assumptions UniprocessorScheduleWithJitter_scheduled_implies_pending_correspondence.
Goal Logic.True. idtac "AUDIT_END UniprocessorScheduleWithJitter_scheduled_implies_pending_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cuj_forall_sched". exact Logic.I. Qed.
Print Assumptions cuj_forall_sched.
Goal Logic.True. idtac "AUDIT_END cuj_forall_sched". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cuj_forall_par". exact Logic.I. Qed.
Print Assumptions cuj_forall_par.
Goal Logic.True. idtac "AUDIT_END cuj_forall_par". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cuj_ico". exact Logic.I. Qed.
Print Assumptions cuj_ico.
Goal Logic.True. idtac "AUDIT_END cuj_ico". exact Logic.I. Qed.
