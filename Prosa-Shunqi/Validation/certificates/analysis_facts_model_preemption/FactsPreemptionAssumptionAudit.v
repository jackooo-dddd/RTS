From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence PreemptionTimeCorrespondence PriorityDrivenCorrespondence PStateCoverHelpers FactsPreemptionCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN preemption_time_interval_case_correspondence". exact Logic.I. Qed.
Print Assumptions preemption_time_interval_case_correspondence.
Goal Logic.True. idtac "AUDIT_END preemption_time_interval_case_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN idle_time_is_pt_correspondence". exact Logic.I. Qed.
Print Assumptions idle_time_is_pt_correspondence.
Goal Logic.True. idtac "AUDIT_END idle_time_is_pt_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN zero_is_pt_correspondence". exact Logic.I. Qed.
Print Assumptions zero_is_pt_correspondence.
Goal Logic.True. idtac "AUDIT_END zero_is_pt_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN first_moment_is_pt_correspondence". exact Logic.I. Qed.
Print Assumptions first_moment_is_pt_correspondence.
Goal Logic.True. idtac "AUDIT_END first_moment_is_pt_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN neg_pt_scheduled_at_correspondence". exact Logic.I. Qed.
Print Assumptions neg_pt_scheduled_at_correspondence.
Goal Logic.True. idtac "AUDIT_END neg_pt_scheduled_at_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN neg_pt_scheduled_before_correspondence". exact Logic.I. Qed.
Print Assumptions neg_pt_scheduled_before_correspondence.
Goal Logic.True. idtac "AUDIT_END neg_pt_scheduled_before_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN neg_pt_scheduled_continuously_before_correspondence". exact Logic.I. Qed.
Print Assumptions neg_pt_scheduled_continuously_before_correspondence.
Goal Logic.True. idtac "AUDIT_END neg_pt_scheduled_continuously_before_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN neg_pt_scheduled_continuously_after_correspondence". exact Logic.I. Qed.
Print Assumptions neg_pt_scheduled_continuously_after_correspondence.
Goal Logic.True. idtac "AUDIT_END neg_pt_scheduled_continuously_after_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN neg_pt_scheduled_continuous_correspondence". exact Logic.I. Qed.
Print Assumptions neg_pt_scheduled_continuous_correspondence.
Goal Logic.True. idtac "AUDIT_END neg_pt_scheduled_continuous_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN neq_scheduled_at_pt_correspondence". exact Logic.I. Qed.
Print Assumptions neq_scheduled_at_pt_correspondence.
Goal Logic.True. idtac "AUDIT_END neq_scheduled_at_pt_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN neq_scheduled_at_pt_continuous_sched_correspondence". exact Logic.I. Qed.
Print Assumptions neq_scheduled_at_pt_continuous_sched_correspondence.
Goal Logic.True. idtac "AUDIT_END neq_scheduled_at_pt_continuous_sched_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN scheduling_of_any_segment_starts_with_preemption_time_correspondence". exact Logic.I. Qed.
Print Assumptions scheduling_of_any_segment_starts_with_preemption_time_correspondence.
Goal Logic.True. idtac "AUDIT_END scheduling_of_any_segment_starts_with_preemption_time_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN scheduling_of_any_segment_starts_with_preemption_time_continuously_sched_correspondence". exact Logic.I. Qed.
Print Assumptions scheduling_of_any_segment_starts_with_preemption_time_continuously_sched_correspondence.
Goal Logic.True. idtac "AUDIT_END scheduling_of_any_segment_starts_with_preemption_time_continuously_sched_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN priority_higher_than_pending_job_priority_correspondence". exact Logic.I. Qed.
Print Assumptions priority_higher_than_pending_job_priority_correspondence.
Goal Logic.True. idtac "AUDIT_END priority_higher_than_pending_job_priority_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fpre_or_correspondence". exact Logic.I. Qed.
Print Assumptions fpre_or_correspondence.
Goal Logic.True. idtac "AUDIT_END fpre_or_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fpre_exists2_correspondence". exact Logic.I. Qed.
Print Assumptions fpre_exists2_correspondence.
Goal Logic.True. idtac "AUDIT_END fpre_exists2_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fpre_and_true_right". exact Logic.I. Qed.
Print Assumptions fpre_and_true_right.
Goal Logic.True. idtac "AUDIT_END fpre_and_true_right". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fpre_neq_related". exact Logic.I. Qed.
Print Assumptions fpre_neq_related.
Goal Logic.True. idtac "AUDIT_END fpre_neq_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fpre_and_absorb_target". exact Logic.I. Qed.
Print Assumptions fpre_and_absorb_target.
Goal Logic.True. idtac "AUDIT_END fpre_and_absorb_target". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fpre_and_absorb_source". exact Logic.I. Qed.
Print Assumptions fpre_and_absorb_source.
Goal Logic.True. idtac "AUDIT_END fpre_and_absorb_source". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fpre_bool_true_of_rel". exact Logic.I. Qed.
Print Assumptions fpre_bool_true_of_rel.
Goal Logic.True. idtac "AUDIT_END fpre_bool_true_of_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fpre_reorder_jr". exact Logic.I. Qed.
Print Assumptions fpre_reorder_jr.
Goal Logic.True. idtac "AUDIT_END fpre_reorder_jr". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fpre_forall_arr". exact Logic.I. Qed.
Print Assumptions fpre_forall_arr.
Goal Logic.True. idtac "AUDIT_END fpre_forall_arr". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fpre_forall_jp". exact Logic.I. Qed.
Print Assumptions fpre_forall_jp.
Goal Logic.True. idtac "AUDIT_END fpre_forall_jp". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fpre_forall_jlfp". exact Logic.I. Qed.
Print Assumptions fpre_forall_jlfp.
Goal Logic.True. idtac "AUDIT_END fpre_forall_jlfp". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fpre_reflexive_rel". exact Logic.I. Qed.
Print Assumptions fpre_reflexive_rel.
Goal Logic.True. idtac "AUDIT_END fpre_reflexive_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fpre_forall_sched". exact Logic.I. Qed.
Print Assumptions fpre_forall_sched.
Goal Logic.True. idtac "AUDIT_END fpre_forall_sched". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fpre_scheduled_at_related". exact Logic.I. Qed.
Print Assumptions fpre_scheduled_at_related.
Goal Logic.True. idtac "AUDIT_END fpre_scheduled_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fpre_service_related". exact Logic.I. Qed.
Print Assumptions fpre_service_related.
Goal Logic.True. idtac "AUDIT_END fpre_service_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fpre_completed_by_related". exact Logic.I. Qed.
Print Assumptions fpre_completed_by_related.
Goal Logic.True. idtac "AUDIT_END fpre_completed_by_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fpre_pending_related". exact Logic.I. Qed.
Print Assumptions fpre_pending_related.
Goal Logic.True. idtac "AUDIT_END fpre_pending_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fpre_come_from_rel". exact Logic.I. Qed.
Print Assumptions fpre_come_from_rel.
Goal Logic.True. idtac "AUDIT_END fpre_come_from_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fpre_must_arrive_rel". exact Logic.I. Qed.
Print Assumptions fpre_must_arrive_rel.
Goal Logic.True. idtac "AUDIT_END fpre_must_arrive_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fpre_is_idle_related". exact Logic.I. Qed.
Print Assumptions fpre_is_idle_related.
Goal Logic.True. idtac "AUDIT_END fpre_is_idle_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fpre_pt_case". exact Logic.I. Qed.
Print Assumptions fpre_pt_case.
Goal Logic.True. idtac "AUDIT_END fpre_pt_case". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fpre_preemption_time_related". exact Logic.I. Qed.
Print Assumptions fpre_preemption_time_related.
Goal Logic.True. idtac "AUDIT_END fpre_preemption_time_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fpre_valid_preemption_model_rel". exact Logic.I. Qed.
Print Assumptions fpre_valid_preemption_model_rel.
Goal Logic.True. idtac "AUDIT_END fpre_valid_preemption_model_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fpre_jr_to_target_rel". exact Logic.I. Qed.
Print Assumptions fpre_jr_to_target_rel.
Goal Logic.True. idtac "AUDIT_END fpre_jr_to_target_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fpre_jr_to_source_rel". exact Logic.I. Qed.
Print Assumptions fpre_jr_to_source_rel.
Goal Logic.True. idtac "AUDIT_END fpre_jr_to_source_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fpre_forall_jr". exact Logic.I. Qed.
Print Assumptions fpre_forall_jr.
Goal Logic.True. idtac "AUDIT_END fpre_forall_jr". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fpre_valid_schedule_rel". exact Logic.I. Qed.
Print Assumptions fpre_valid_schedule_rel.
Goal Logic.True. idtac "AUDIT_END fpre_valid_schedule_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fpre_backlogged_related". exact Logic.I. Qed.
Print Assumptions fpre_backlogged_related.
Goal Logic.True. idtac "AUDIT_END fpre_backlogged_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fpre_respects_jlfp_rel". exact Logic.I. Qed.
Print Assumptions fpre_respects_jlfp_rel.
Goal Logic.True. idtac "AUDIT_END fpre_respects_jlfp_rel". exact Logic.I. Qed.
