From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations CriterionCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN schedulability_transferred_correspondence". exact Logic.I. Qed.
Print Assumptions schedulability_transferred_correspondence.
Goal Logic.True. idtac "AUDIT_END schedulability_transferred_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN deadlines_met_correspondence". exact Logic.I. Qed.
Print Assumptions deadlines_met_correspondence.
Goal Logic.True. idtac "AUDIT_END deadlines_met_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ref_cost_bounds_online_cost_correspondence". exact Logic.I. Qed.
Print Assumptions ref_cost_bounds_online_cost_correspondence.
Goal Logic.True. idtac "AUDIT_END ref_cost_bounds_online_cost_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN remaining_cost_bound_correspondence". exact Logic.I. Qed.
Print Assumptions remaining_cost_bound_correspondence.
Goal Logic.True. idtac "AUDIT_END remaining_cost_bound_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN remcost_service_correspondence". exact Logic.I. Qed.
Print Assumptions remcost_service_correspondence.
Goal Logic.True. idtac "AUDIT_END remcost_service_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN remcost_service_during_correspondence". exact Logic.I. Qed.
Print Assumptions remcost_service_during_correspondence.
Goal Logic.True. idtac "AUDIT_END remcost_service_during_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN remcost_total_service_during_correspondence". exact Logic.I. Qed.
Print Assumptions remcost_total_service_during_correspondence.
Goal Logic.True. idtac "AUDIT_END remcost_total_service_during_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN remaining_cost_invariant_correspondence". exact Logic.I. Qed.
Print Assumptions remaining_cost_invariant_correspondence.
Goal Logic.True. idtac "AUDIT_END remaining_cost_invariant_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN online_remaining_cost_bounded_correspondence". exact Logic.I. Qed.
Print Assumptions online_remaining_cost_bounded_correspondence.
Goal Logic.True. idtac "AUDIT_END online_remaining_cost_bounded_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN remaining_cost_positive_correspondence". exact Logic.I. Qed.
Print Assumptions remaining_cost_positive_correspondence.
Goal Logic.True. idtac "AUDIT_END remaining_cost_positive_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN remaining_cost_zero_correspondence". exact Logic.I. Qed.
Print Assumptions remaining_cost_zero_correspondence.
Goal Logic.True. idtac "AUDIT_END remaining_cost_zero_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN critical_jobs_correspondence". exact Logic.I. Qed.
Print Assumptions critical_jobs_correspondence.
Goal Logic.True. idtac "AUDIT_END critical_jobs_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN critical_jobs_monotonicity_correspondence". exact Logic.I. Qed.
Print Assumptions critical_jobs_monotonicity_correspondence.
Goal Logic.True. idtac "AUDIT_END critical_jobs_monotonicity_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN critical_jobs_dropout_correspondence". exact Logic.I. Qed.
Print Assumptions critical_jobs_dropout_correspondence.
Goal Logic.True. idtac "AUDIT_END critical_jobs_dropout_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN critical_jobs_filter_complete_correspondence". exact Logic.I. Qed.
Print Assumptions critical_jobs_filter_complete_correspondence.
Goal Logic.True. idtac "AUDIT_END critical_jobs_filter_complete_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN critical_jobs_uniq_correspondence". exact Logic.I. Qed.
Print Assumptions critical_jobs_uniq_correspondence.
Goal Logic.True. idtac "AUDIT_END critical_jobs_uniq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN critical_jobs_min_completion_time_correspondence". exact Logic.I. Qed.
Print Assumptions critical_jobs_min_completion_time_correspondence.
Goal Logic.True. idtac "AUDIT_END critical_jobs_min_completion_time_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN critical_jobs_remaining_cost_monotonic_correspondence". exact Logic.I. Qed.
Print Assumptions critical_jobs_remaining_cost_monotonic_correspondence.
Goal Logic.True. idtac "AUDIT_END critical_jobs_remaining_cost_monotonic_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN slackless_interval_correspondence". exact Logic.I. Qed.
Print Assumptions slackless_interval_correspondence.
Goal Logic.True. idtac "AUDIT_END slackless_interval_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN contiguously_slackless_interval_correspondence". exact Logic.I. Qed.
Print Assumptions contiguously_slackless_interval_correspondence.
Goal Logic.True. idtac "AUDIT_END contiguously_slackless_interval_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN transfer_schedulability_criterion_correspondence". exact Logic.I. Qed.
Print Assumptions transfer_schedulability_criterion_correspondence.
Goal Logic.True. idtac "AUDIT_END transfer_schedulability_criterion_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN late_in_critical_jobs_correspondence". exact Logic.I. Qed.
Print Assumptions late_in_critical_jobs_correspondence.
Goal Logic.True. idtac "AUDIT_END late_in_critical_jobs_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN late_not_at_start_correspondence". exact Logic.I. Qed.
Print Assumptions late_not_at_start_correspondence.
Goal Logic.True. idtac "AUDIT_END late_not_at_start_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN nonpositive_slack_correspondence". exact Logic.I. Qed.
Print Assumptions nonpositive_slack_correspondence.
Goal Logic.True. idtac "AUDIT_END nonpositive_slack_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN contiguously_nps_correspondence". exact Logic.I. Qed.
Print Assumptions contiguously_nps_correspondence.
Goal Logic.True. idtac "AUDIT_END contiguously_nps_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN contiguously_nps_start_correspondence". exact Logic.I. Qed.
Print Assumptions contiguously_nps_start_correspondence.
Goal Logic.True. idtac "AUDIT_END contiguously_nps_start_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN contiguously_nps_existence_correspondence". exact Logic.I. Qed.
Print Assumptions contiguously_nps_existence_correspondence.
Goal Logic.True. idtac "AUDIT_END contiguously_nps_existence_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN slackless_interval_step_case_completed_job_rem_correspondence". exact Logic.I. Qed.
Print Assumptions slackless_interval_step_case_completed_job_rem_correspondence.
Goal Logic.True. idtac "AUDIT_END slackless_interval_step_case_completed_job_rem_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN slackless_interval_step_case_completed_job_correspondence". exact Logic.I. Qed.
Print Assumptions slackless_interval_step_case_completed_job_correspondence.
Goal Logic.True. idtac "AUDIT_END slackless_interval_step_case_completed_job_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN slackless_interval_step_case_incomplete_job_correspondence". exact Logic.I. Qed.
Print Assumptions slackless_interval_step_case_incomplete_job_correspondence.
Goal Logic.True. idtac "AUDIT_END slackless_interval_step_case_incomplete_job_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN slackless_interval_step_correspondence". exact Logic.I. Qed.
Print Assumptions slackless_interval_step_correspondence.
Goal Logic.True. idtac "AUDIT_END slackless_interval_step_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN slackless_interval_continuation_correspondence". exact Logic.I. Qed.
Print Assumptions slackless_interval_continuation_correspondence.
Goal Logic.True. idtac "AUDIT_END slackless_interval_continuation_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN slackless_interval_existence_correspondence". exact Logic.I. Qed.
Print Assumptions slackless_interval_existence_correspondence.
Goal Logic.True. idtac "AUDIT_END slackless_interval_existence_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN slackless_interval_completion_correspondence". exact Logic.I. Qed.
Print Assumptions slackless_interval_completion_correspondence.
Goal Logic.True. idtac "AUDIT_END slackless_interval_completion_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN online_transfer_schedulability_criterion_sufficiency_correspondence". exact Logic.I. Qed.
Print Assumptions online_transfer_schedulability_criterion_sufficiency_correspondence.
Goal Logic.True. idtac "AUDIT_END online_transfer_schedulability_criterion_sufficiency_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN online_transfer_schedulability_criterion_ensures_schedulability_correspondence". exact Logic.I. Qed.
Print Assumptions online_transfer_schedulability_criterion_ensures_schedulability_correspondence.
Goal Logic.True. idtac "AUDIT_END online_transfer_schedulability_criterion_ensures_schedulability_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN delay_if_no_critical_job_is_scheduled_correspondence". exact Logic.I. Qed.
Print Assumptions delay_if_no_critical_job_is_scheduled_correspondence.
Goal Logic.True. idtac "AUDIT_END delay_if_no_critical_job_is_scheduled_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN online_transfer_schedulability_criterion_necessity_correspondence". exact Logic.I. Qed.
Print Assumptions online_transfer_schedulability_criterion_necessity_correspondence.
Goal Logic.True. idtac "AUDIT_END online_transfer_schedulability_criterion_necessity_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ref_transfer_schedulability_criterion_sufficiency_correspondence". exact Logic.I. Qed.
Print Assumptions ref_transfer_schedulability_criterion_sufficiency_correspondence.
Goal Logic.True. idtac "AUDIT_END ref_transfer_schedulability_criterion_sufficiency_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ref_transfer_schedulability_criterion_ensures_schedulability_correspondence". exact Logic.I. Qed.
Print Assumptions ref_transfer_schedulability_criterion_ensures_schedulability_correspondence.
Goal Logic.True. idtac "AUDIT_END ref_transfer_schedulability_criterion_ensures_schedulability_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_forall_cover_sprop". exact Logic.I. Qed.
Print Assumptions id_forall_cover_sprop.
Goal Logic.True. idtac "AUDIT_END id_forall_cover_sprop". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_lean_transport". exact Logic.I. Qed.
Print Assumptions id_lean_transport.
Goal Logic.True. idtac "AUDIT_END id_lean_transport". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_nat_input". exact Logic.I. Qed.
Print Assumptions id_nat_input.
Goal Logic.True. idtac "AUDIT_END id_nat_input". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_bool_eq_correspondence". exact Logic.I. Qed.
Print Assumptions id_bool_eq_correspondence.
Goal Logic.True. idtac "AUDIT_END id_bool_eq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_nat_eq_correspondence". exact Logic.I. Qed.
Print Assumptions id_nat_eq_correspondence.
Goal Logic.True. idtac "AUDIT_END id_nat_eq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_or_correspondence". exact Logic.I. Qed.
Print Assumptions id_or_correspondence.
Goal Logic.True. idtac "AUDIT_END id_or_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_not_correspondence". exact Logic.I. Qed.
Print Assumptions id_not_correspondence.
Goal Logic.True. idtac "AUDIT_END id_not_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_exists_identity_correspondence". exact Logic.I. Qed.
Print Assumptions id_exists_identity_correspondence.
Goal Logic.True. idtac "AUDIT_END id_exists_identity_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_eq_identity_correspondence". exact Logic.I. Qed.
Print Assumptions id_eq_identity_correspondence.
Goal Logic.True. idtac "AUDIT_END id_eq_identity_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_opt_source_roundtrip". exact Logic.I. Qed.
Print Assumptions id_opt_source_roundtrip.
Goal Logic.True. idtac "AUDIT_END id_opt_source_roundtrip". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_opt_target_roundtrip". exact Logic.I. Qed.
Print Assumptions id_opt_target_roundtrip.
Goal Logic.True. idtac "AUDIT_END id_opt_target_roundtrip". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_opt_rel_canonical". exact Logic.I. Qed.
Print Assumptions id_opt_rel_canonical.
Goal Logic.True. idtac "AUDIT_END id_opt_rel_canonical". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_opt_rel_surjective". exact Logic.I. Qed.
Print Assumptions id_opt_rel_surjective.
Goal Logic.True. idtac "AUDIT_END id_opt_rel_surjective". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_opt_eq_correspondence". exact Logic.I. Qed.
Print Assumptions id_opt_eq_correspondence.
Goal Logic.True. idtac "AUDIT_END id_opt_eq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_option_some_eq_correspondence". exact Logic.I. Qed.
Print Assumptions id_option_some_eq_correspondence.
Goal Logic.True. idtac "AUDIT_END id_option_some_eq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_option_none_eq_related". exact Logic.I. Qed.
Print Assumptions id_option_none_eq_related.
Goal Logic.True. idtac "AUDIT_END id_option_none_eq_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_src_scheduled_on". exact Logic.I. Qed.
Print Assumptions id_src_scheduled_on.
Goal Logic.True. idtac "AUDIT_END id_src_scheduled_on". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_src_scheduled_in". exact Logic.I. Qed.
Print Assumptions id_src_scheduled_in.
Goal Logic.True. idtac "AUDIT_END id_src_scheduled_in". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_src_service_in". exact Logic.I. Qed.
Print Assumptions id_src_service_in.
Goal Logic.True. idtac "AUDIT_END id_src_service_in". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_src_supply_in". exact Logic.I. Qed.
Print Assumptions id_src_supply_in.
Goal Logic.True. idtac "AUDIT_END id_src_supply_in". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_scheduled_in_related". exact Logic.I. Qed.
Print Assumptions id_scheduled_in_related.
Goal Logic.True. idtac "AUDIT_END id_scheduled_in_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_decide_state_related". exact Logic.I. Qed.
Print Assumptions id_decide_state_related.
Goal Logic.True. idtac "AUDIT_END id_decide_state_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_service_on_related". exact Logic.I. Qed.
Print Assumptions id_service_on_related.
Goal Logic.True. idtac "AUDIT_END id_service_on_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_service_in_related". exact Logic.I. Qed.
Print Assumptions id_service_in_related.
Goal Logic.True. idtac "AUDIT_END id_service_in_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_supply_in_related". exact Logic.I. Qed.
Print Assumptions id_supply_in_related.
Goal Logic.True. idtac "AUDIT_END id_supply_in_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_core_rel_surjective". exact Logic.I. Qed.
Print Assumptions id_core_rel_surjective.
Goal Logic.True. idtac "AUDIT_END id_core_rel_surjective". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_schedule_to_target_rel". exact Logic.I. Qed.
Print Assumptions id_schedule_to_target_rel.
Goal Logic.True. idtac "AUDIT_END id_schedule_to_target_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_schedule_to_source_rel". exact Logic.I. Qed.
Print Assumptions id_schedule_to_source_rel.
Goal Logic.True. idtac "AUDIT_END id_schedule_to_source_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_scheduled_at_related". exact Logic.I. Qed.
Print Assumptions id_scheduled_at_related.
Goal Logic.True. idtac "AUDIT_END id_scheduled_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_service_at_related". exact Logic.I. Qed.
Print Assumptions id_service_at_related.
Goal Logic.True. idtac "AUDIT_END id_service_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_ideal_is_idle_related". exact Logic.I. Qed.
Print Assumptions id_ideal_is_idle_related.
Goal Logic.True. idtac "AUDIT_END id_ideal_is_idle_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_scheduled_at_state_related". exact Logic.I. Qed.
Print Assumptions id_scheduled_at_state_related.
Goal Logic.True. idtac "AUDIT_END id_scheduled_at_state_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cr_service_at_fun". exact Logic.I. Qed.
Print Assumptions cr_service_at_fun.
Goal Logic.True. idtac "AUDIT_END cr_service_at_fun". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cr_service_during_related". exact Logic.I. Qed.
Print Assumptions cr_service_during_related.
Goal Logic.True. idtac "AUDIT_END cr_service_during_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cr_service_related". exact Logic.I. Qed.
Print Assumptions cr_service_related.
Goal Logic.True. idtac "AUDIT_END cr_service_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cr_completed_by_related". exact Logic.I. Qed.
Print Assumptions cr_completed_by_related.
Goal Logic.True. idtac "AUDIT_END cr_completed_by_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cr_remaining_cost_related". exact Logic.I. Qed.
Print Assumptions cr_remaining_cost_related.
Goal Logic.True. idtac "AUDIT_END cr_remaining_cost_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cr_cde_rel". exact Logic.I. Qed.
Print Assumptions cr_cde_rel.
Goal Logic.True. idtac "AUDIT_END cr_cde_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cr_big_seq_as_fold". exact Logic.I. Qed.
Print Assumptions cr_big_seq_as_fold.
Goal Logic.True. idtac "AUDIT_END cr_big_seq_as_fold". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cr_sumseq_canonical". exact Logic.I. Qed.
Print Assumptions cr_sumseq_canonical.
Goal Logic.True. idtac "AUDIT_END cr_sumseq_canonical". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cr_sumseq_related". exact Logic.I. Qed.
Print Assumptions cr_sumseq_related.
Goal Logic.True. idtac "AUDIT_END cr_sumseq_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cr_sumtrue_canonical". exact Logic.I. Qed.
Print Assumptions cr_sumtrue_canonical.
Goal Logic.True. idtac "AUDIT_END cr_sumtrue_canonical". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cr_sumtrue_related". exact Logic.I. Qed.
Print Assumptions cr_sumtrue_related.
Goal Logic.True. idtac "AUDIT_END cr_sumtrue_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cr_forall_ord_all". exact Logic.I. Qed.
Print Assumptions cr_forall_ord_all.
Goal Logic.True. idtac "AUDIT_END cr_forall_ord_all". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cr_all_nat_canonical". exact Logic.I. Qed.
Print Assumptions cr_all_nat_canonical.
Goal Logic.True. idtac "AUDIT_END cr_all_nat_canonical". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cr_forall_ord_related". exact Logic.I. Qed.
Print Assumptions cr_forall_ord_related.
Goal Logic.True. idtac "AUDIT_END cr_forall_ord_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cr_list_eq_correspondence". exact Logic.I. Qed.
Print Assumptions cr_list_eq_correspondence.
Goal Logic.True. idtac "AUDIT_END cr_list_eq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cr_forall_list". exact Logic.I. Qed.
Print Assumptions cr_forall_list.
Goal Logic.True. idtac "AUDIT_END cr_forall_list". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cr_forall_cost". exact Logic.I. Qed.
Print Assumptions cr_forall_cost.
Goal Logic.True. idtac "AUDIT_END cr_forall_cost". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cr_cost_le_rel". exact Logic.I. Qed.
Print Assumptions cr_cost_le_rel.
Goal Logic.True. idtac "AUDIT_END cr_cost_le_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cr_jobs_come_from_rel". exact Logic.I. Qed.
Print Assumptions cr_jobs_come_from_rel.
Goal Logic.True. idtac "AUDIT_END cr_jobs_come_from_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cr_jobs_must_arrive_rel". exact Logic.I. Qed.
Print Assumptions cr_jobs_must_arrive_rel.
Goal Logic.True. idtac "AUDIT_END cr_jobs_must_arrive_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cr_job_meets_deadline_related". exact Logic.I. Qed.
Print Assumptions cr_job_meets_deadline_related.
Goal Logic.True. idtac "AUDIT_END cr_job_meets_deadline_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cr_succ_related". exact Logic.I. Qed.
Print Assumptions cr_succ_related.
Goal Logic.True. idtac "AUDIT_END cr_succ_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cr_pred_related". exact Logic.I. Qed.
Print Assumptions cr_pred_related.
Goal Logic.True. idtac "AUDIT_END cr_pred_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cr_sum_rcb_related". exact Logic.I. Qed.
Print Assumptions cr_sum_rcb_related.
Goal Logic.True. idtac "AUDIT_END cr_sum_rcb_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cr_service_of_jobs_true_related". exact Logic.I. Qed.
Print Assumptions cr_service_of_jobs_true_related.
Goal Logic.True. idtac "AUDIT_END cr_service_of_jobs_true_related". exact Logic.I. Qed.
