From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations FactsCompletionCorrespondence.

Goal Logic.True. idtac "AUDIT_BEGIN completion_monotonic_correspondence". exact Logic.I. Qed.
Print Assumptions completion_monotonic_correspondence.
Goal Logic.True. idtac "AUDIT_END completion_monotonic_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN incompletion_monotonic_correspondence". exact Logic.I. Qed.
Print Assumptions incompletion_monotonic_correspondence.
Goal Logic.True. idtac "AUDIT_END incompletion_monotonic_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN less_service_than_cost_is_incomplete_correspondence". exact Logic.I. Qed.
Print Assumptions less_service_than_cost_is_incomplete_correspondence.
Goal Logic.True. idtac "AUDIT_END less_service_than_cost_is_incomplete_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN incomplete_is_positive_remaining_cost_correspondence". exact Logic.I. Qed.
Print Assumptions incomplete_is_positive_remaining_cost_correspondence.
Goal Logic.True. idtac "AUDIT_END incomplete_is_positive_remaining_cost_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN incomplete_implies_positive_cost_correspondence". exact Logic.I. Qed.
Print Assumptions incomplete_implies_positive_cost_correspondence.
Goal Logic.True. idtac "AUDIT_END incomplete_implies_positive_cost_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN scheduled_implies_positive_cost_correspondence". exact Logic.I. Qed.
Print Assumptions scheduled_implies_positive_cost_correspondence.
Goal Logic.True. idtac "AUDIT_END scheduled_implies_positive_cost_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_lt_cost_correspondence". exact Logic.I. Qed.
Print Assumptions service_lt_cost_correspondence.
Goal Logic.True. idtac "AUDIT_END service_lt_cost_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN serviced_implies_positive_remaining_cost_correspondence". exact Logic.I. Qed.
Print Assumptions serviced_implies_positive_remaining_cost_correspondence.
Goal Logic.True. idtac "AUDIT_END serviced_implies_positive_remaining_cost_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN scheduled_implies_positive_remaining_cost_correspondence". exact Logic.I. Qed.
Print Assumptions scheduled_implies_positive_remaining_cost_correspondence.
Goal Logic.True. idtac "AUDIT_END scheduled_implies_positive_remaining_cost_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN scheduled_implies_not_completed_correspondence". exact Logic.I. Qed.
Print Assumptions scheduled_implies_not_completed_correspondence.
Goal Logic.True. idtac "AUDIT_END scheduled_implies_not_completed_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN not_scheduled_remains_incomplete_correspondence". exact Logic.I. Qed.
Print Assumptions not_scheduled_remains_incomplete_correspondence.
Goal Logic.True. idtac "AUDIT_END not_scheduled_remains_incomplete_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN completed_implies_not_scheduled_correspondence". exact Logic.I. Qed.
Print Assumptions completed_implies_not_scheduled_correspondence.
Goal Logic.True. idtac "AUDIT_END completed_implies_not_scheduled_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN completed_on_arrival_implies_zero_cost_correspondence". exact Logic.I. Qed.
Print Assumptions completed_on_arrival_implies_zero_cost_correspondence.
Goal Logic.True. idtac "AUDIT_END completed_on_arrival_implies_zero_cost_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN not_pending_earlier_and_at_0_correspondence". exact Logic.I. Qed.
Print Assumptions not_pending_earlier_and_at_0_correspondence.
Goal Logic.True. idtac "AUDIT_END not_pending_earlier_and_at_0_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN completed_implies_scheduled_before_correspondence". exact Logic.I. Qed.
Print Assumptions completed_implies_scheduled_before_correspondence.
Goal Logic.True. idtac "AUDIT_END completed_implies_scheduled_before_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_pending_at_arrival_correspondence". exact Logic.I. Qed.
Print Assumptions job_pending_at_arrival_correspondence.
Goal Logic.True. idtac "AUDIT_END job_pending_at_arrival_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN has_arrived_scheduled_correspondence". exact Logic.I. Qed.
Print Assumptions has_arrived_scheduled_correspondence.
Goal Logic.True. idtac "AUDIT_END has_arrived_scheduled_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_at_most_cost_correspondence". exact Logic.I. Qed.
Print Assumptions service_at_most_cost_correspondence.
Goal Logic.True. idtac "AUDIT_END service_at_most_cost_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_cost_invariant_correspondence". exact Logic.I. Qed.
Print Assumptions service_cost_invariant_correspondence.
Goal Logic.True. idtac "AUDIT_END service_cost_invariant_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cumulative_service_le_job_cost_correspondence". exact Logic.I. Qed.
Print Assumptions cumulative_service_le_job_cost_correspondence.
Goal Logic.True. idtac "AUDIT_END cumulative_service_le_job_cost_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_doesnt_complete_before_remaining_cost_correspondence". exact Logic.I. Qed.
Print Assumptions job_doesnt_complete_before_remaining_cost_correspondence.
Goal Logic.True. idtac "AUDIT_END job_doesnt_complete_before_remaining_cost_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN scheduled_implies_pending_correspondence". exact Logic.I. Qed.
Print Assumptions scheduled_implies_pending_correspondence.
Goal Logic.True. idtac "AUDIT_END scheduled_implies_pending_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ready_implies_incomplete_correspondence". exact Logic.I. Qed.
Print Assumptions ready_implies_incomplete_correspondence.
Goal Logic.True. idtac "AUDIT_END ready_implies_incomplete_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN completed_jobs_are_not_ready_correspondence". exact Logic.I. Qed.
Print Assumptions completed_jobs_are_not_ready_correspondence.
Goal Logic.True. idtac "AUDIT_END completed_jobs_are_not_ready_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN valid_schedule_implies_completed_jobs_dont_execute_correspondence". exact Logic.I. Qed.
Print Assumptions valid_schedule_implies_completed_jobs_dont_execute_correspondence.
Goal Logic.True. idtac "AUDIT_END valid_schedule_implies_completed_jobs_dont_execute_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ideal_progress_completed_jobs_correspondence". exact Logic.I. Qed.
Print Assumptions ideal_progress_completed_jobs_correspondence.
Goal Logic.True. idtac "AUDIT_END ideal_progress_completed_jobs_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN scheduled_implies_serviced_correspondence". exact Logic.I. Qed.
Print Assumptions scheduled_implies_serviced_correspondence.
Goal Logic.True. idtac "AUDIT_END scheduled_implies_serviced_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN unit_service_correspondence". exact Logic.I. Qed.
Print Assumptions unit_service_correspondence.
Goal Logic.True. idtac "AUDIT_END unit_service_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN identical_prefix_completed_by_correspondence". exact Logic.I. Qed.
Print Assumptions identical_prefix_completed_by_correspondence.
Goal Logic.True. idtac "AUDIT_END identical_prefix_completed_by_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN identical_prefix_pending_correspondence". exact Logic.I. Qed.
Print Assumptions identical_prefix_pending_correspondence.
Goal Logic.True. idtac "AUDIT_END identical_prefix_pending_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fc_forall_cover_sprop". exact Logic.I. Qed.
Print Assumptions fc_forall_cover_sprop.
Goal Logic.True. idtac "AUDIT_END fc_forall_cover_sprop". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fc_iff_correspondence". exact Logic.I. Qed.
Print Assumptions fc_iff_correspondence.
Goal Logic.True. idtac "AUDIT_END fc_iff_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fc_lean_transport". exact Logic.I. Qed.
Print Assumptions fc_lean_transport.
Goal Logic.True. idtac "AUDIT_END fc_lean_transport". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fc_nat_input". exact Logic.I. Qed.
Print Assumptions fc_nat_input.
Goal Logic.True. idtac "AUDIT_END fc_nat_input". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fc_bool_eq_correspondence". exact Logic.I. Qed.
Print Assumptions fc_bool_eq_correspondence.
Goal Logic.True. idtac "AUDIT_END fc_bool_eq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fc_succ_related". exact Logic.I. Qed.
Print Assumptions fc_succ_related.
Goal Logic.True. idtac "AUDIT_END fc_succ_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fc_scheduled_at_related". exact Logic.I. Qed.
Print Assumptions fc_scheduled_at_related.
Goal Logic.True. idtac "AUDIT_END fc_scheduled_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fc_service_at_related". exact Logic.I. Qed.
Print Assumptions fc_service_at_related.
Goal Logic.True. idtac "AUDIT_END fc_service_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fc_service_during_related". exact Logic.I. Qed.
Print Assumptions fc_service_during_related.
Goal Logic.True. idtac "AUDIT_END fc_service_during_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fc_service_related". exact Logic.I. Qed.
Print Assumptions fc_service_related.
Goal Logic.True. idtac "AUDIT_END fc_service_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fc_completed_by_related". exact Logic.I. Qed.
Print Assumptions fc_completed_by_related.
Goal Logic.True. idtac "AUDIT_END fc_completed_by_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fc_remaining_cost_related". exact Logic.I. Qed.
Print Assumptions fc_remaining_cost_related.
Goal Logic.True. idtac "AUDIT_END fc_remaining_cost_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fc_completed_jobs_dont_execute_related". exact Logic.I. Qed.
Print Assumptions fc_completed_jobs_dont_execute_related.
Goal Logic.True. idtac "AUDIT_END fc_completed_jobs_dont_execute_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fc_has_arrived_related". exact Logic.I. Qed.
Print Assumptions fc_has_arrived_related.
Goal Logic.True. idtac "AUDIT_END fc_has_arrived_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fc_jobs_must_arrive_related". exact Logic.I. Qed.
Print Assumptions fc_jobs_must_arrive_related.
Goal Logic.True. idtac "AUDIT_END fc_jobs_must_arrive_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fc_pending_related". exact Logic.I. Qed.
Print Assumptions fc_pending_related.
Goal Logic.True. idtac "AUDIT_END fc_pending_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fc_pending_earlier_and_at_related". exact Logic.I. Qed.
Print Assumptions fc_pending_earlier_and_at_related.
Goal Logic.True. idtac "AUDIT_END fc_pending_earlier_and_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fc_ideal_progress_rel". exact Logic.I. Qed.
Print Assumptions fc_ideal_progress_rel.
Goal Logic.True. idtac "AUDIT_END fc_ideal_progress_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fc_unit_service_rel". exact Logic.I. Qed.
Print Assumptions fc_unit_service_rel.
Goal Logic.True. idtac "AUDIT_END fc_unit_service_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fc_jobs_must_be_ready_related". exact Logic.I. Qed.
Print Assumptions fc_jobs_must_be_ready_related.
Goal Logic.True. idtac "AUDIT_END fc_jobs_must_be_ready_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fc_arrival_sequence_to_source_rel". exact Logic.I. Qed.
Print Assumptions fc_arrival_sequence_to_source_rel.
Goal Logic.True. idtac "AUDIT_END fc_arrival_sequence_to_source_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fc_schedule_fun_to_svc". exact Logic.I. Qed.
Print Assumptions fc_schedule_fun_to_svc.
Goal Logic.True. idtac "AUDIT_END fc_schedule_fun_to_svc". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fc_schedule_to_target_rel". exact Logic.I. Qed.
Print Assumptions fc_schedule_to_target_rel.
Goal Logic.True. idtac "AUDIT_END fc_schedule_to_target_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fc_schedule_to_source_rel". exact Logic.I. Qed.
Print Assumptions fc_schedule_to_source_rel.
Goal Logic.True. idtac "AUDIT_END fc_schedule_to_source_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fc_identical_prefix_correspondence". exact Logic.I. Qed.
Print Assumptions fc_identical_prefix_correspondence.
Goal Logic.True. idtac "AUDIT_END fc_identical_prefix_correspondence". exact Logic.I. Qed.
