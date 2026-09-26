From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence.

Goal Logic.True. idtac "AUDIT_BEGIN JobPreemptable_source_total". exact Logic.I. Qed.
Print Assumptions JobPreemptable_source_total.
Goal Logic.True. idtac "AUDIT_END JobPreemptable_source_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN JobPreemptable_target_total". exact Logic.I. Qed.
Print Assumptions JobPreemptable_target_total.
Goal Logic.True. idtac "AUDIT_END JobPreemptable_target_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_preemption_points_correspondence". exact Logic.I. Qed.
Print Assumptions job_preemption_points_correspondence.
Goal Logic.True. idtac "AUDIT_END job_preemption_points_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN conversion_preserves_equivalence_correspondence". exact Logic.I. Qed.
Print Assumptions conversion_preserves_equivalence_correspondence.
Goal Logic.True. idtac "AUDIT_END conversion_preserves_equivalence_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN lengths_of_segments_correspondence". exact Logic.I. Qed.
Print Assumptions lengths_of_segments_correspondence.
Goal Logic.True. idtac "AUDIT_END lengths_of_segments_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_max_nonpreemptive_segment_correspondence". exact Logic.I. Qed.
Print Assumptions job_max_nonpreemptive_segment_correspondence.
Goal Logic.True. idtac "AUDIT_END job_max_nonpreemptive_segment_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_last_nonpreemptive_segment_correspondence". exact Logic.I. Qed.
Print Assumptions job_last_nonpreemptive_segment_correspondence.
Goal Logic.True. idtac "AUDIT_END job_last_nonpreemptive_segment_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_rtct_correspondence". exact Logic.I. Qed.
Print Assumptions job_rtct_correspondence.
Goal Logic.True. idtac "AUDIT_END job_rtct_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN preempted_at_correspondence". exact Logic.I. Qed.
Print Assumptions preempted_at_correspondence.
Goal Logic.True. idtac "AUDIT_END preempted_at_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_cannot_become_nonpreemptive_before_execution_correspondence". exact Logic.I. Qed.
Print Assumptions job_cannot_become_nonpreemptive_before_execution_correspondence.
Goal Logic.True. idtac "AUDIT_END job_cannot_become_nonpreemptive_before_execution_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_cannot_be_nonpreemptive_after_completion_correspondence". exact Logic.I. Qed.
Print Assumptions job_cannot_be_nonpreemptive_after_completion_correspondence.
Goal Logic.True. idtac "AUDIT_END job_cannot_be_nonpreemptive_after_completion_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN not_preemptive_implies_scheduled_correspondence". exact Logic.I. Qed.
Print Assumptions not_preemptive_implies_scheduled_correspondence.
Goal Logic.True. idtac "AUDIT_END not_preemptive_implies_scheduled_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN execution_starts_with_preemption_point_correspondence". exact Logic.I. Qed.
Print Assumptions execution_starts_with_preemption_point_correspondence.
Goal Logic.True. idtac "AUDIT_END execution_starts_with_preemption_point_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN valid_preemption_model_correspondence". exact Logic.I. Qed.
Print Assumptions valid_preemption_model_correspondence.
Goal Logic.True. idtac "AUDIT_END valid_preemption_model_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN no_superfluous_preemptions_correspondence". exact Logic.I. Qed.
Print Assumptions no_superfluous_preemptions_correspondence.
Goal Logic.True. idtac "AUDIT_END no_superfluous_preemptions_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pp_nat_input". exact Logic.I. Qed.
Print Assumptions pp_nat_input.
Goal Logic.True. idtac "AUDIT_END pp_nat_input". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pp_succ_related". exact Logic.I. Qed.
Print Assumptions pp_succ_related.
Goal Logic.True. idtac "AUDIT_END pp_succ_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pp_iff_correspondence". exact Logic.I. Qed.
Print Assumptions pp_iff_correspondence.
Goal Logic.True. idtac "AUDIT_END pp_iff_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pp_filter_canonical". exact Logic.I. Qed.
Print Assumptions pp_filter_canonical.
Goal Logic.True. idtac "AUDIT_END pp_filter_canonical". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pp_filter_related". exact Logic.I. Qed.
Print Assumptions pp_filter_related.
Goal Logic.True. idtac "AUDIT_END pp_filter_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pp_range_related". exact Logic.I. Qed.
Print Assumptions pp_range_related.
Goal Logic.True. idtac "AUDIT_END pp_range_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pp_nat_eq_transport". exact Logic.I. Qed.
Print Assumptions pp_nat_eq_transport.
Goal Logic.True. idtac "AUDIT_END pp_nat_eq_transport". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pp_nat_eqb_related". exact Logic.I. Qed.
Print Assumptions pp_nat_eqb_related.
Goal Logic.True. idtac "AUDIT_END pp_nat_eqb_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pp_bool_or_canonical". exact Logic.I. Qed.
Print Assumptions pp_bool_or_canonical.
Goal Logic.True. idtac "AUDIT_END pp_bool_or_canonical". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pp_bool_or_related". exact Logic.I. Qed.
Print Assumptions pp_bool_or_related.
Goal Logic.True. idtac "AUDIT_END pp_bool_or_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pp_mem_canonical". exact Logic.I. Qed.
Print Assumptions pp_mem_canonical.
Goal Logic.True. idtac "AUDIT_END pp_mem_canonical". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pp_mem_related". exact Logic.I. Qed.
Print Assumptions pp_mem_related.
Goal Logic.True. idtac "AUDIT_END pp_mem_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pp_distances_canonical". exact Logic.I. Qed.
Print Assumptions pp_distances_canonical.
Goal Logic.True. idtac "AUDIT_END pp_distances_canonical". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pp_distances_related". exact Logic.I. Qed.
Print Assumptions pp_distances_related.
Goal Logic.True. idtac "AUDIT_END pp_distances_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pp_max_canonical". exact Logic.I. Qed.
Print Assumptions pp_max_canonical.
Goal Logic.True. idtac "AUDIT_END pp_max_canonical". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pp_foldmax_canonical". exact Logic.I. Qed.
Print Assumptions pp_foldmax_canonical.
Goal Logic.True. idtac "AUDIT_END pp_foldmax_canonical". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pp_max0_related". exact Logic.I. Qed.
Print Assumptions pp_max0_related.
Goal Logic.True. idtac "AUDIT_END pp_max0_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pp_last0_canonical". exact Logic.I. Qed.
Print Assumptions pp_last0_canonical.
Goal Logic.True. idtac "AUDIT_END pp_last0_canonical". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pp_last0_related". exact Logic.I. Qed.
Print Assumptions pp_last0_related.
Goal Logic.True. idtac "AUDIT_END pp_last0_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pp_scheduled_at_related". exact Logic.I. Qed.
Print Assumptions pp_scheduled_at_related.
Goal Logic.True. idtac "AUDIT_END pp_scheduled_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pp_service_at_related". exact Logic.I. Qed.
Print Assumptions pp_service_at_related.
Goal Logic.True. idtac "AUDIT_END pp_service_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pp_service_related". exact Logic.I. Qed.
Print Assumptions pp_service_related.
Goal Logic.True. idtac "AUDIT_END pp_service_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pp_completed_by_related". exact Logic.I. Qed.
Print Assumptions pp_completed_by_related.
Goal Logic.True. idtac "AUDIT_END pp_completed_by_related". exact Logic.I. Qed.
