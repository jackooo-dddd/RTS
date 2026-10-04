From FoundationCertificates Require Import ClassicUniLimitedPlatformCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN LimitedPreemptionPlatform_preemption_time_correspondence". exact Logic.I. Qed.
Print Assumptions LimitedPreemptionPlatform_preemption_time_correspondence.
Goal Logic.True. idtac "AUDIT_END LimitedPreemptionPlatform_preemption_time_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN LimitedPreemptionPlatform_not_preemptive_implies_scheduled_correspondence". exact Logic.I. Qed.
Print Assumptions LimitedPreemptionPlatform_not_preemptive_implies_scheduled_correspondence.
Goal Logic.True. idtac "AUDIT_END LimitedPreemptionPlatform_not_preemptive_implies_scheduled_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN LimitedPreemptionPlatform_execution_starts_with_preemption_point_correspondence". exact Logic.I. Qed.
Print Assumptions LimitedPreemptionPlatform_execution_starts_with_preemption_point_correspondence.
Goal Logic.True. idtac "AUDIT_END LimitedPreemptionPlatform_execution_starts_with_preemption_point_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN LimitedPreemptionPlatform_correct_preemption_model_correspondence". exact Logic.I. Qed.
Print Assumptions LimitedPreemptionPlatform_correct_preemption_model_correspondence.
Goal Logic.True. idtac "AUDIT_END LimitedPreemptionPlatform_correct_preemption_model_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN LimitedPreemptionPlatform_job_cannot_become_nonpreemptive_before_execution_correspondence". exact Logic.I. Qed.
Print Assumptions LimitedPreemptionPlatform_job_cannot_become_nonpreemptive_before_execution_correspondence.
Goal Logic.True. idtac "AUDIT_END LimitedPreemptionPlatform_job_cannot_become_nonpreemptive_before_execution_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN LimitedPreemptionPlatform_job_cannot_be_nonpreemptive_after_completion_correspondence". exact Logic.I. Qed.
Print Assumptions LimitedPreemptionPlatform_job_cannot_be_nonpreemptive_after_completion_correspondence.
Goal Logic.True. idtac "AUDIT_END LimitedPreemptionPlatform_job_cannot_be_nonpreemptive_after_completion_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN LimitedPreemptionPlatform_job_max_nonpreemptive_segment_le_task_max_nonpreemptive_segment_correspondence". exact Logic.I. Qed.
Print Assumptions LimitedPreemptionPlatform_job_max_nonpreemptive_segment_le_task_max_nonpreemptive_segment_correspondence.
Goal Logic.True. idtac "AUDIT_END LimitedPreemptionPlatform_job_max_nonpreemptive_segment_le_task_max_nonpreemptive_segment_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN LimitedPreemptionPlatform_nonpreemptive_regions_have_bounded_length_correspondence". exact Logic.I. Qed.
Print Assumptions LimitedPreemptionPlatform_nonpreemptive_regions_have_bounded_length_correspondence.
Goal Logic.True. idtac "AUDIT_END LimitedPreemptionPlatform_nonpreemptive_regions_have_bounded_length_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN LimitedPreemptionPlatform_model_with_bounded_nonpreemptive_segments_correspondence". exact Logic.I. Qed.
Print Assumptions LimitedPreemptionPlatform_model_with_bounded_nonpreemptive_segments_correspondence.
Goal Logic.True. idtac "AUDIT_END LimitedPreemptionPlatform_model_with_bounded_nonpreemptive_segments_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN LimitedPreemptionPlatform_zero_is_pt_correspondence". exact Logic.I. Qed.
Print Assumptions LimitedPreemptionPlatform_zero_is_pt_correspondence.
Goal Logic.True. idtac "AUDIT_END LimitedPreemptionPlatform_zero_is_pt_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN LimitedPreemptionPlatform_first_moment_is_pt_correspondence". exact Logic.I. Qed.
Print Assumptions LimitedPreemptionPlatform_first_moment_is_pt_correspondence.
Goal Logic.True. idtac "AUDIT_END LimitedPreemptionPlatform_first_moment_is_pt_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN LimitedPreemptionPlatform_work_conserving_correspondence". exact Logic.I. Qed.
Print Assumptions LimitedPreemptionPlatform_work_conserving_correspondence.
Goal Logic.True. idtac "AUDIT_END LimitedPreemptionPlatform_work_conserving_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN LimitedPreemptionPlatform_respects_FP_policy_at_preemption_point_correspondence". exact Logic.I. Qed.
Print Assumptions LimitedPreemptionPlatform_respects_FP_policy_at_preemption_point_correspondence.
Goal Logic.True. idtac "AUDIT_END LimitedPreemptionPlatform_respects_FP_policy_at_preemption_point_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN LimitedPreemptionPlatform_respects_JLFP_policy_at_preemption_point_correspondence". exact Logic.I. Qed.
Print Assumptions LimitedPreemptionPlatform_respects_JLFP_policy_at_preemption_point_correspondence.
Goal Logic.True. idtac "AUDIT_END LimitedPreemptionPlatform_respects_JLFP_policy_at_preemption_point_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cdp_forall_sched". exact Logic.I. Qed.
Print Assumptions cdp_forall_sched.
Goal Logic.True. idtac "AUDIT_END cdp_forall_sched". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cdp_forall_par". exact Logic.I. Qed.
Print Assumptions cdp_forall_par.
Goal Logic.True. idtac "AUDIT_END cdp_forall_par". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cdp_ico". exact Logic.I. Qed.
Print Assumptions cdp_ico.
Goal Logic.True. idtac "AUDIT_END cdp_ico". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cdp_forall_pm". exact Logic.I. Qed.
Print Assumptions cdp_forall_pm.
Goal Logic.True. idtac "AUDIT_END cdp_forall_pm". exact Logic.I. Qed.
