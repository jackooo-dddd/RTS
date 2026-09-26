From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations FactsSwapsCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN trivial_swap_correspondence". exact Logic.I. Qed.
Print Assumptions trivial_swap_correspondence.
Goal Logic.True. idtac "AUDIT_END trivial_swap_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN trivial_swap_service_invariant_correspondence". exact Logic.I. Qed.
Print Assumptions trivial_swap_service_invariant_correspondence.
Goal Logic.True. idtac "AUDIT_END trivial_swap_service_invariant_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN swap_other_times_invariant_correspondence". exact Logic.I. Qed.
Print Assumptions swap_other_times_invariant_correspondence.
Goal Logic.True. idtac "AUDIT_END swap_other_times_invariant_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN swap_job_scheduled_t1_correspondence". exact Logic.I. Qed.
Print Assumptions swap_job_scheduled_t1_correspondence.
Goal Logic.True. idtac "AUDIT_END swap_job_scheduled_t1_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN swap_job_scheduled_t2_correspondence". exact Logic.I. Qed.
Print Assumptions swap_job_scheduled_t2_correspondence.
Goal Logic.True. idtac "AUDIT_END swap_job_scheduled_t2_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN swap_job_scheduled_other_times_correspondence". exact Logic.I. Qed.
Print Assumptions swap_job_scheduled_other_times_correspondence.
Goal Logic.True. idtac "AUDIT_END swap_job_scheduled_other_times_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN swap_job_scheduled_cases_correspondence". exact Logic.I. Qed.
Print Assumptions swap_job_scheduled_cases_correspondence.
Goal Logic.True. idtac "AUDIT_END swap_job_scheduled_cases_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN swap_job_scheduled_correspondence". exact Logic.I. Qed.
Print Assumptions swap_job_scheduled_correspondence.
Goal Logic.True. idtac "AUDIT_END swap_job_scheduled_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN swap_job_scheduled_original_cases_correspondence". exact Logic.I. Qed.
Print Assumptions swap_job_scheduled_original_cases_correspondence.
Goal Logic.True. idtac "AUDIT_END swap_job_scheduled_original_cases_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN swap_job_scheduled_original_correspondence". exact Logic.I. Qed.
Print Assumptions swap_job_scheduled_original_correspondence.
Goal Logic.True. idtac "AUDIT_END swap_job_scheduled_original_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN swap_before_invariant_correspondence". exact Logic.I. Qed.
Print Assumptions swap_before_invariant_correspondence.
Goal Logic.True. idtac "AUDIT_END swap_before_invariant_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN swap_after_invariant_correspondence". exact Logic.I. Qed.
Print Assumptions swap_after_invariant_correspondence.
Goal Logic.True. idtac "AUDIT_END swap_after_invariant_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_before_swap_invariant_correspondence". exact Logic.I. Qed.
Print Assumptions service_before_swap_invariant_correspondence.
Goal Logic.True. idtac "AUDIT_END service_before_swap_invariant_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_after_swap_invariant_correspondence". exact Logic.I. Qed.
Print Assumptions service_after_swap_invariant_correspondence.
Goal Logic.True. idtac "AUDIT_END service_after_swap_invariant_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_of_others_invariant_correspondence". exact Logic.I. Qed.
Print Assumptions service_of_others_invariant_correspondence.
Goal Logic.True. idtac "AUDIT_END service_of_others_invariant_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN swapped_service_bound_correspondence". exact Logic.I. Qed.
Print Assumptions swapped_service_bound_correspondence.
Goal Logic.True. idtac "AUDIT_END swapped_service_bound_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN swapped_completed_jobs_dont_execute_correspondence". exact Logic.I. Qed.
Print Assumptions swapped_completed_jobs_dont_execute_correspondence.
Goal Logic.True. idtac "AUDIT_END swapped_completed_jobs_dont_execute_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN swapped_jobs_come_from_arrival_sequence_correspondence". exact Logic.I. Qed.
Print Assumptions swapped_jobs_come_from_arrival_sequence_correspondence.
Goal Logic.True. idtac "AUDIT_END swapped_jobs_come_from_arrival_sequence_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN uninvolved_implies_deadline_met_correspondence". exact Logic.I. Qed.
Print Assumptions uninvolved_implies_deadline_met_correspondence.
Goal Logic.True. idtac "AUDIT_END uninvolved_implies_deadline_met_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN moved_earlier_implies_deadline_met_correspondence". exact Logic.I. Qed.
Print Assumptions moved_earlier_implies_deadline_met_correspondence.
Goal Logic.True. idtac "AUDIT_END moved_earlier_implies_deadline_met_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN moved_later_implies_deadline_met_correspondence". exact Logic.I. Qed.
Print Assumptions moved_later_implies_deadline_met_correspondence.
Goal Logic.True. idtac "AUDIT_END moved_later_implies_deadline_met_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN edf_swap_no_deadline_misses_introduced_correspondence". exact Logic.I. Qed.
Print Assumptions edf_swap_no_deadline_misses_introduced_correspondence.
Goal Logic.True. idtac "AUDIT_END edf_swap_no_deadline_misses_introduced_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN swp_forall_cover_sprop". exact Logic.I. Qed.
Print Assumptions swp_forall_cover_sprop.
Goal Logic.True. idtac "AUDIT_END swp_forall_cover_sprop". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN swp_nat_input". exact Logic.I. Qed.
Print Assumptions swp_nat_input.
Goal Logic.True. idtac "AUDIT_END swp_nat_input". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN swp_lean_transport". exact Logic.I. Qed.
Print Assumptions swp_lean_transport.
Goal Logic.True. idtac "AUDIT_END swp_lean_transport". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN swp_false_correspondence". exact Logic.I. Qed.
Print Assumptions swp_false_correspondence.
Goal Logic.True. idtac "AUDIT_END swp_false_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN swp_nat_neq_correspondence". exact Logic.I. Qed.
Print Assumptions swp_nat_neq_correspondence.
Goal Logic.True. idtac "AUDIT_END swp_nat_neq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN swp_or_correspondence". exact Logic.I. Qed.
Print Assumptions swp_or_correspondence.
Goal Logic.True. idtac "AUDIT_END swp_or_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN swp_bool_eq_correspondence". exact Logic.I. Qed.
Print Assumptions swp_bool_eq_correspondence.
Goal Logic.True. idtac "AUDIT_END swp_bool_eq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN swp_exists_identity". exact Logic.I. Qed.
Print Assumptions swp_exists_identity.
Goal Logic.True. idtac "AUDIT_END swp_exists_identity". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN swp_decide_not". exact Logic.I. Qed.
Print Assumptions swp_decide_not.
Goal Logic.True. idtac "AUDIT_END swp_decide_not". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN swp_nat_neqb_related". exact Logic.I. Qed.
Print Assumptions swp_nat_neqb_related.
Goal Logic.True. idtac "AUDIT_END swp_nat_neqb_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN swp_state_rel". exact Logic.I. Qed.
Print Assumptions swp_state_rel.
Goal Logic.True. idtac "AUDIT_END swp_state_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN swp_state_eq_correspondence". exact Logic.I. Qed.
Print Assumptions swp_state_eq_correspondence.
Goal Logic.True. idtac "AUDIT_END swp_state_eq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN swp_nat_not_eq". exact Logic.I. Qed.
Print Assumptions swp_nat_not_eq.
Goal Logic.True. idtac "AUDIT_END swp_nat_not_eq". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN swp_src_same". exact Logic.I. Qed.
Print Assumptions swp_src_same.
Goal Logic.True. idtac "AUDIT_END swp_src_same". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN swp_src_other". exact Logic.I. Qed.
Print Assumptions swp_src_other.
Goal Logic.True. idtac "AUDIT_END swp_src_other". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN swp_replace_at_fun". exact Logic.I. Qed.
Print Assumptions swp_replace_at_fun.
Goal Logic.True. idtac "AUDIT_END swp_replace_at_fun". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN swp_swapped_fun". exact Logic.I. Qed.
Print Assumptions swp_swapped_fun.
Goal Logic.True. idtac "AUDIT_END swp_swapped_fun". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN swp_scheduled_at_related". exact Logic.I. Qed.
Print Assumptions swp_scheduled_at_related.
Goal Logic.True. idtac "AUDIT_END swp_scheduled_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN swp_service_at_related". exact Logic.I. Qed.
Print Assumptions swp_service_at_related.
Goal Logic.True. idtac "AUDIT_END swp_service_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN swp_service_related". exact Logic.I. Qed.
Print Assumptions swp_service_related.
Goal Logic.True. idtac "AUDIT_END swp_service_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN swp_completed_jobs_dont_execute_related". exact Logic.I. Qed.
Print Assumptions swp_completed_jobs_dont_execute_related.
Goal Logic.True. idtac "AUDIT_END swp_completed_jobs_dont_execute_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN swp_service_bound_related". exact Logic.I. Qed.
Print Assumptions swp_service_bound_related.
Goal Logic.True. idtac "AUDIT_END swp_service_bound_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN swp_job_meets_deadline_related". exact Logic.I. Qed.
Print Assumptions swp_job_meets_deadline_related.
Goal Logic.True. idtac "AUDIT_END swp_job_meets_deadline_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN swp_unit_service_related". exact Logic.I. Qed.
Print Assumptions swp_unit_service_related.
Goal Logic.True. idtac "AUDIT_END swp_unit_service_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN swp_ideal_progress_related". exact Logic.I. Qed.
Print Assumptions swp_ideal_progress_related.
Goal Logic.True. idtac "AUDIT_END swp_ideal_progress_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN swp_arrival_sequence_to_source_rel". exact Logic.I. Qed.
Print Assumptions swp_arrival_sequence_to_source_rel.
Goal Logic.True. idtac "AUDIT_END swp_arrival_sequence_to_source_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN swp_cases_related". exact Logic.I. Qed.
Print Assumptions swp_cases_related.
Goal Logic.True. idtac "AUDIT_END swp_cases_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN swp_original_cases_related". exact Logic.I. Qed.
Print Assumptions swp_original_cases_related.
Goal Logic.True. idtac "AUDIT_END swp_original_cases_related". exact Logic.I. Qed.
