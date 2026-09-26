From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence FactsRtcJobPreemptableCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN preemption_points_of_zero_cost_job_correspondence". exact Logic.I. Qed.
Print Assumptions preemption_points_of_zero_cost_job_correspondence.
Goal Logic.True. idtac "AUDIT_END preemption_points_of_zero_cost_job_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN zero_in_preemption_points_correspondence". exact Logic.I. Qed.
Print Assumptions zero_in_preemption_points_correspondence.
Goal Logic.True. idtac "AUDIT_END zero_in_preemption_points_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_cost_in_preemption_points_correspondence". exact Logic.I. Qed.
Print Assumptions job_cost_in_preemption_points_correspondence.
Goal Logic.True. idtac "AUDIT_END job_cost_in_preemption_points_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN size_of_preemption_points_correspondence". exact Logic.I. Qed.
Print Assumptions size_of_preemption_points_correspondence.
Goal Logic.True. idtac "AUDIT_END size_of_preemption_points_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN preemption_points_nondecreasing_correspondence". exact Logic.I. Qed.
Print Assumptions preemption_points_nondecreasing_correspondence.
Goal Logic.True. idtac "AUDIT_END preemption_points_nondecreasing_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_cost_is_last_element_of_preemption_points_correspondence". exact Logic.I. Qed.
Print Assumptions job_cost_is_last_element_of_preemption_points_correspondence.
Goal Logic.True. idtac "AUDIT_END job_cost_is_last_element_of_preemption_points_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_last_nonpreemptive_segment_positive_correspondence". exact Logic.I. Qed.
Print Assumptions job_last_nonpreemptive_segment_positive_correspondence.
Goal Logic.True. idtac "AUDIT_END job_last_nonpreemptive_segment_positive_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_max_nonpreemptive_segment_positive_correspondence". exact Logic.I. Qed.
Print Assumptions job_max_nonpreemptive_segment_positive_correspondence.
Goal Logic.True. idtac "AUDIT_END job_max_nonpreemptive_segment_positive_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_max_nonpreemptive_segment_le_job_cost_correspondence". exact Logic.I. Qed.
Print Assumptions job_max_nonpreemptive_segment_le_job_cost_correspondence.
Goal Logic.True. idtac "AUDIT_END job_max_nonpreemptive_segment_le_job_cost_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_last_nonpreemptive_segment_le_job_cost_correspondence". exact Logic.I. Qed.
Print Assumptions job_last_nonpreemptive_segment_le_job_cost_correspondence.
Goal Logic.True. idtac "AUDIT_END job_last_nonpreemptive_segment_le_job_cost_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_run_to_completion_threshold_positive_correspondence". exact Logic.I. Qed.
Print Assumptions job_run_to_completion_threshold_positive_correspondence.
Goal Logic.True. idtac "AUDIT_END job_run_to_completion_threshold_positive_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_run_to_completion_threshold_le_job_cost_correspondence". exact Logic.I. Qed.
Print Assumptions job_run_to_completion_threshold_le_job_cost_correspondence.
Goal Logic.True. idtac "AUDIT_END job_run_to_completion_threshold_le_job_cost_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_cannot_be_preempted_within_last_segment_correspondence". exact Logic.I. Qed.
Print Assumptions job_cannot_be_preempted_within_last_segment_correspondence.
Goal Logic.True. idtac "AUDIT_END job_cannot_be_preempted_within_last_segment_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_nonpreemptive_after_run_to_completion_threshold_correspondence". exact Logic.I. Qed.
Print Assumptions job_nonpreemptive_after_run_to_completion_threshold_correspondence.
Goal Logic.True. idtac "AUDIT_END job_nonpreemptive_after_run_to_completion_threshold_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frtc_length_canonical". exact Logic.I. Qed.
Print Assumptions frtc_length_canonical.
Goal Logic.True. idtac "AUDIT_END frtc_length_canonical". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frtc_length_related". exact Logic.I. Qed.
Print Assumptions frtc_length_related.
Goal Logic.True. idtac "AUDIT_END frtc_length_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frtc_nthD_canonical". exact Logic.I. Qed.
Print Assumptions frtc_nthD_canonical.
Goal Logic.True. idtac "AUDIT_END frtc_nthD_canonical". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frtc_nthD_related". exact Logic.I. Qed.
Print Assumptions frtc_nthD_related.
Goal Logic.True. idtac "AUDIT_END frtc_nthD_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frtc_nondecreasing_sequence_related". exact Logic.I. Qed.
Print Assumptions frtc_nondecreasing_sequence_related.
Goal Logic.True. idtac "AUDIT_END frtc_nondecreasing_sequence_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frtc_nat_list_to_rocq". exact Logic.I. Qed.
Print Assumptions frtc_nat_list_to_rocq.
Goal Logic.True. idtac "AUDIT_END frtc_nat_list_to_rocq". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frtc_nat_list_source_roundtrip". exact Logic.I. Qed.
Print Assumptions frtc_nat_list_source_roundtrip.
Goal Logic.True. idtac "AUDIT_END frtc_nat_list_source_roundtrip". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frtc_list_eq_correspondence". exact Logic.I. Qed.
Print Assumptions frtc_list_eq_correspondence.
Goal Logic.True. idtac "AUDIT_END frtc_list_eq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frtc_cost_positive_related". exact Logic.I. Qed.
Print Assumptions frtc_cost_positive_related.
Goal Logic.True. idtac "AUDIT_END frtc_cost_positive_related". exact Logic.I. Qed.
