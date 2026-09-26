From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence TaskPreemptionParametersCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN TaskMaxNonpreemptiveSegment_source_total". exact Logic.I. Qed.
Print Assumptions TaskMaxNonpreemptiveSegment_source_total.
Goal Logic.True. idtac "AUDIT_END TaskMaxNonpreemptiveSegment_source_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN TaskMaxNonpreemptiveSegment_target_total". exact Logic.I. Qed.
Print Assumptions TaskMaxNonpreemptiveSegment_target_total.
Goal Logic.True. idtac "AUDIT_END TaskMaxNonpreemptiveSegment_target_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN TaskRunToCompletionThreshold_source_total". exact Logic.I. Qed.
Print Assumptions TaskRunToCompletionThreshold_source_total.
Goal Logic.True. idtac "AUDIT_END TaskRunToCompletionThreshold_source_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN TaskRunToCompletionThreshold_target_total". exact Logic.I. Qed.
Print Assumptions TaskRunToCompletionThreshold_target_total.
Goal Logic.True. idtac "AUDIT_END TaskRunToCompletionThreshold_target_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN TaskPreemptionPoints_source_total". exact Logic.I. Qed.
Print Assumptions TaskPreemptionPoints_source_total.
Goal Logic.True. idtac "AUDIT_END TaskPreemptionPoints_source_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN TaskPreemptionPoints_target_total". exact Logic.I. Qed.
Print Assumptions TaskPreemptionPoints_target_total.
Goal Logic.True. idtac "AUDIT_END TaskPreemptionPoints_target_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN task_max_nonpr_segment_correspondence". exact Logic.I. Qed.
Print Assumptions task_max_nonpr_segment_correspondence.
Goal Logic.True. idtac "AUDIT_END task_max_nonpr_segment_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN task_last_nonpr_segment_correspondence". exact Logic.I. Qed.
Print Assumptions task_last_nonpr_segment_correspondence.
Goal Logic.True. idtac "AUDIT_END task_last_nonpr_segment_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN TaskPreemptionPoints_to_TaskMaxNonpreemptiveSegment_conversion_correspondence". exact Logic.I. Qed.
Print Assumptions TaskPreemptionPoints_to_TaskMaxNonpreemptiveSegment_conversion_correspondence.
Goal Logic.True. idtac "AUDIT_END TaskPreemptionPoints_to_TaskMaxNonpreemptiveSegment_conversion_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_respects_max_nonpreemptive_segment_correspondence". exact Logic.I. Qed.
Print Assumptions job_respects_max_nonpreemptive_segment_correspondence.
Goal Logic.True. idtac "AUDIT_END job_respects_max_nonpreemptive_segment_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN nonpreemptive_regions_have_bounded_length_correspondence". exact Logic.I. Qed.
Print Assumptions nonpreemptive_regions_have_bounded_length_correspondence.
Goal Logic.True. idtac "AUDIT_END nonpreemptive_regions_have_bounded_length_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN model_with_bounded_nonpreemptive_segments_correspondence". exact Logic.I. Qed.
Print Assumptions model_with_bounded_nonpreemptive_segments_correspondence.
Goal Logic.True. idtac "AUDIT_END model_with_bounded_nonpreemptive_segments_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN valid_model_with_bounded_nonpreemptive_segments_correspondence". exact Logic.I. Qed.
Print Assumptions valid_model_with_bounded_nonpreemptive_segments_correspondence.
Goal Logic.True. idtac "AUDIT_END valid_model_with_bounded_nonpreemptive_segments_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN task_rtc_bounded_by_cost_correspondence". exact Logic.I. Qed.
Print Assumptions task_rtc_bounded_by_cost_correspondence.
Goal Logic.True. idtac "AUDIT_END task_rtc_bounded_by_cost_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_respects_task_rtc_correspondence". exact Logic.I. Qed.
Print Assumptions job_respects_task_rtc_correspondence.
Goal Logic.True. idtac "AUDIT_END job_respects_task_rtc_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN valid_task_run_to_completion_threshold_correspondence". exact Logic.I. Qed.
Print Assumptions valid_task_run_to_completion_threshold_correspondence.
Goal Logic.True. idtac "AUDIT_END valid_task_run_to_completion_threshold_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN tpp_lean_transport". exact Logic.I. Qed.
Print Assumptions tpp_lean_transport.
Goal Logic.True. idtac "AUDIT_END tpp_lean_transport". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN tpp_logic_eq_to_lean_eq". exact Logic.I. Qed.
Print Assumptions tpp_logic_eq_to_lean_eq.
Goal Logic.True. idtac "AUDIT_END tpp_logic_eq_to_lean_eq". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN tpp_decide_eq_related". exact Logic.I. Qed.
Print Assumptions tpp_decide_eq_related.
Goal Logic.True. idtac "AUDIT_END tpp_decide_eq_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN tpp_nat_list_to_rocq". exact Logic.I. Qed.
Print Assumptions tpp_nat_list_to_rocq.
Goal Logic.True. idtac "AUDIT_END tpp_nat_list_to_rocq". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN tpp_nat_list_target_roundtrip". exact Logic.I. Qed.
Print Assumptions tpp_nat_list_target_roundtrip.
Goal Logic.True. idtac "AUDIT_END tpp_nat_list_target_roundtrip". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN tpp_job_of_task_related". exact Logic.I. Qed.
Print Assumptions tpp_job_of_task_related.
Goal Logic.True. idtac "AUDIT_END tpp_job_of_task_related". exact Logic.I. Qed.
