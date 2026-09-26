From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence LimitedPreemptiveCorrespondence TaskPreemptionParametersCorrespondence TaskLimitedPreemptiveCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN task_beginning_of_execution_in_preemption_points_correspondence". exact Logic.I. Qed.
Print Assumptions task_beginning_of_execution_in_preemption_points_correspondence.
Goal Logic.True. idtac "AUDIT_END task_beginning_of_execution_in_preemption_points_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN task_end_of_execution_in_preemption_points_correspondence". exact Logic.I. Qed.
Print Assumptions task_end_of_execution_in_preemption_points_correspondence.
Goal Logic.True. idtac "AUDIT_END task_end_of_execution_in_preemption_points_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN nondecreasing_task_preemption_points_correspondence". exact Logic.I. Qed.
Print Assumptions nondecreasing_task_preemption_points_correspondence.
Goal Logic.True. idtac "AUDIT_END nondecreasing_task_preemption_points_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN consistent_job_segment_count_correspondence". exact Logic.I. Qed.
Print Assumptions consistent_job_segment_count_correspondence.
Goal Logic.True. idtac "AUDIT_END consistent_job_segment_count_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_respects_segment_lengths_correspondence". exact Logic.I. Qed.
Print Assumptions job_respects_segment_lengths_correspondence.
Goal Logic.True. idtac "AUDIT_END job_respects_segment_lengths_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN task_segments_are_nonempty_correspondence". exact Logic.I. Qed.
Print Assumptions task_segments_are_nonempty_correspondence.
Goal Logic.True. idtac "AUDIT_END task_segments_are_nonempty_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN valid_fixed_preemption_points_task_model_correspondence". exact Logic.I. Qed.
Print Assumptions valid_fixed_preemption_points_task_model_correspondence.
Goal Logic.True. idtac "AUDIT_END valid_fixed_preemption_points_task_model_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN valid_fixed_preemption_points_model_correspondence". exact Logic.I. Qed.
Print Assumptions valid_fixed_preemption_points_model_correspondence.
Goal Logic.True. idtac "AUDIT_END valid_fixed_preemption_points_model_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN tlp_first0_canonical". exact Logic.I. Qed.
Print Assumptions tlp_first0_canonical.
Goal Logic.True. idtac "AUDIT_END tlp_first0_canonical". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN tlp_first0_related". exact Logic.I. Qed.
Print Assumptions tlp_first0_related.
Goal Logic.True. idtac "AUDIT_END tlp_first0_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN tlp_limited_preemptions_rtc_threshold_related". exact Logic.I. Qed.
Print Assumptions tlp_limited_preemptions_rtc_threshold_related.
Goal Logic.True. idtac "AUDIT_END tlp_limited_preemptions_rtc_threshold_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN tlp_task_points_of_job_related". exact Logic.I. Qed.
Print Assumptions tlp_task_points_of_job_related.
Goal Logic.True. idtac "AUDIT_END tlp_task_points_of_job_related". exact Logic.I. Qed.
