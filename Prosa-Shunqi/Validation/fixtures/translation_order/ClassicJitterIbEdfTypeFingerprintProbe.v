(* Recomputes the authoritative `Check @name` fingerprints for classic/analysis/global/jitter/interference_bound_edf.v. *)
Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.classic.analysis.global.jitter.interference_bound.
Require Import prosa.classic.analysis.global.jitter.interference_bound_edf.
Require Import prosa.classic.analysis.global.jitter.workload_bound.
Require Import prosa.classic.model.arrival.basic.arrival_sequence.
Require Import prosa.classic.model.arrival.basic.job.
Require Import prosa.classic.model.arrival.basic.task.
Require Import prosa.classic.model.arrival.basic.task_arrival.
Require Import prosa.classic.model.priority.
Require Import prosa.classic.model.schedule.global.basic.interference.
Require Import prosa.classic.model.schedule.global.basic.schedule.
Require Import prosa.classic.model.schedule.global.jitter.interference.
Require Import prosa.classic.model.schedule.global.jitter.interference_edf.
Require Import prosa.classic.model.schedule.global.jitter.job.
Require Import prosa.classic.model.schedule.global.jitter.platform.
Require Import prosa.classic.model.schedule.global.jitter.schedule.
Require Import prosa.classic.model.schedule.global.response_time.
Require Import prosa.classic.model.schedule.global.schedulability.
Require Import prosa.classic.model.schedule.global.workload.
Require Import prosa.classic.model.time.
Require Import prosa.classic.util.all.
Require Import prosa.classic.util.bigcat.
Require Import prosa.classic.util.bigord.
Require Import prosa.classic.util.counting.
Require Import prosa.classic.util.div_mod.
Require Import prosa.classic.util.fixedpoint.
Require Import prosa.classic.util.induction.
Require Import prosa.classic.util.list.
Require Import prosa.classic.util.minmax.
Require Import prosa.classic.util.nat.
Require Import prosa.classic.util.notation.
Require Import prosa.classic.util.ord_quantifier.
Require Import prosa.classic.util.pick.
Require Import prosa.classic.util.powerset.
Require Import prosa.classic.util.seqset.
Require Import prosa.classic.util.sorting.
Require Import prosa.classic.util.ssromega.
Require Import prosa.classic.util.step_function.
Require Import prosa.classic.util.sum.
Require Import prosa.classic.util.tactics.
Require Import prosa.util.bigcat.
Require Import prosa.util.div_mod.
Require Import prosa.util.epsilon.
Require Import prosa.util.list.
Require Import prosa.util.minmax.
Require Import prosa.util.nat.
Require Import prosa.util.notation.
Require Import prosa.util.rel.
Require Import prosa.util.seqset.
Require Import prosa.util.setoid.
Require Import prosa.util.subadditivity.
Require Import prosa.util.sum.
Require Import prosa.util.supremum.
Require Import prosa.util.tactics.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop div path.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.edf_specific_interference_bound". Abort.
Check @prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.edf_specific_interference_bound.
Goal True. idtac "END|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.edf_specific_interference_bound". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf". Abort.
Check @prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf.
Goal True. idtac "END|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.total_interference_bound_edf". Abort.
Check @prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.total_interference_bound_edf.
Goal True. idtac "END|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.total_interference_bound_edf". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_use_another_definition". Abort.
Check @prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_use_another_definition.
Goal True. idtac "END|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_use_another_definition". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_simpl_by_filtering_interfering_jobs". Abort.
Check @prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_simpl_by_filtering_interfering_jobs.
Goal True. idtac "END|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_simpl_by_filtering_interfering_jobs". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_simpl_by_sorting_interfering_jobs". Abort.
Check @prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_simpl_by_sorting_interfering_jobs.
Goal True. idtac "END|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_simpl_by_sorting_interfering_jobs". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_job_in_same_sequence". Abort.
Check @prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_job_in_same_sequence.
Goal True. idtac "END|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_job_in_same_sequence". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_all_jobs_from_tsk_k". Abort.
Check @prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_all_jobs_from_tsk_k.
Goal True. idtac "END|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_all_jobs_from_tsk_k". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_jobs_ordered_by_arrival". Abort.
Check @prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_jobs_ordered_by_arrival.
Goal True. idtac "END|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_jobs_ordered_by_arrival". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_interference_le_task_cost". Abort.
Check @prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_interference_le_task_cost.
Goal True. idtac "END|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_interference_le_task_cost". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_holds_for_at_most_n_k_jobs". Abort.
Check @prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_holds_for_at_most_n_k_jobs.
Goal True. idtac "END|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_holds_for_at_most_n_k_jobs". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_at_least_one_job". Abort.
Check @prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_at_least_one_job.
Goal True. idtac "END|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_at_least_one_job". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_j_fst_is_job_of_tsk_k". Abort.
Check @prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_j_fst_is_job_of_tsk_k.
Goal True. idtac "END|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_j_fst_is_job_of_tsk_k". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_j_fst_deadline". Abort.
Check @prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_j_fst_deadline.
Goal True. idtac "END|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_j_fst_deadline". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_j_i_deadline". Abort.
Check @prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_j_i_deadline.
Goal True. idtac "END|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_j_i_deadline". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_j_fst_completion_implies_rt_bound_inside_interval". Abort.
Check @prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_j_fst_completion_implies_rt_bound_inside_interval.
Goal True. idtac "END|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_j_fst_completion_implies_rt_bound_inside_interval". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_simpl_when_there's_one_job". Abort.
Check @prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_simpl_when_there's_one_job.
Goal True. idtac "END|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_simpl_when_there's_one_job". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_holds_for_single_job_that_completes_on_time". Abort.
Check @prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_holds_for_single_job_that_completes_on_time.
Goal True. idtac "END|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_holds_for_single_job_that_completes_on_time". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_response_time_bound_of_j_fst_after_interval". Abort.
Check @prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_response_time_bound_of_j_fst_after_interval.
Goal True. idtac "END|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_response_time_bound_of_j_fst_after_interval". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_holds_for_single_job_with_big_slack". Abort.
Check @prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_holds_for_single_job_with_big_slack.
Goal True. idtac "END|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_holds_for_single_job_with_big_slack". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_holds_for_single_job_with_small_slack". Abort.
Check @prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_holds_for_single_job_with_small_slack.
Goal True. idtac "END|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_holds_for_single_job_with_small_slack". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_interference_of_j_fst_limited_by_slack". Abort.
Check @prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_interference_of_j_fst_limited_by_slack.
Goal True. idtac "END|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_interference_of_j_fst_limited_by_slack". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_holds_for_a_single_job". Abort.
Check @prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_holds_for_a_single_job.
Goal True. idtac "END|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_holds_for_a_single_job". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_j_lst_is_job_of_tsk_k". Abort.
Check @prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_j_lst_is_job_of_tsk_k.
Goal True. idtac "END|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_j_lst_is_job_of_tsk_k". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_j_lst_deadline". Abort.
Check @prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_j_lst_deadline.
Goal True. idtac "END|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_j_lst_deadline". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_j_fst_before_j_lst". Abort.
Check @prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_j_fst_before_j_lst.
Goal True. idtac "END|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_j_fst_before_j_lst". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_last_job_arrives_before_end_of_interval". Abort.
Check @prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_last_job_arrives_before_end_of_interval.
Goal True. idtac "END|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_last_job_arrives_before_end_of_interval". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_j_fst_completed_on_time". Abort.
Check @prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_j_fst_completed_on_time.
Goal True. idtac "END|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_j_fst_completed_on_time". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_many_periods_in_between". Abort.
Check @prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_many_periods_in_between.
Goal True. idtac "END|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_many_periods_in_between". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_n_k_covers_middle_jobs_plus_one". Abort.
Check @prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_n_k_covers_middle_jobs_plus_one.
Goal True. idtac "END|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_n_k_covers_middle_jobs_plus_one". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_holds_for_middle_and_last_jobs". Abort.
Check @prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_holds_for_middle_and_last_jobs.
Goal True. idtac "END|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_holds_for_middle_and_last_jobs". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_n_k_equals_num_mid_jobs_plus_one". Abort.
Check @prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_n_k_equals_num_mid_jobs_plus_one.
Goal True. idtac "END|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_n_k_equals_num_mid_jobs_plus_one". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_remainder_ge_slack". Abort.
Check @prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_remainder_ge_slack.
Goal True. idtac "END|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_remainder_ge_slack". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_simpl_by_moving_to_left_side". Abort.
Check @prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_simpl_by_moving_to_left_side.
Goal True. idtac "END|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_simpl_by_moving_to_left_side". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_interference_of_j_fst_bounded_by_response_time". Abort.
Check @prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_interference_of_j_fst_bounded_by_response_time.
Goal True. idtac "END|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_interference_of_j_fst_bounded_by_response_time". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_bounding_interference_with_interval_lengths". Abort.
Check @prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_bounding_interference_with_interval_lengths.
Goal True. idtac "END|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_bounding_interference_with_interval_lengths". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_simpl_by_concatenation_of_intervals". Abort.
Check @prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_simpl_by_concatenation_of_intervals.
Goal True. idtac "END|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_simpl_by_concatenation_of_intervals". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_interference_of_j_fst_limited_by_remainder_and_slack". Abort.
Check @prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_interference_of_j_fst_limited_by_remainder_and_slack.
Goal True. idtac "END|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_interference_of_j_fst_limited_by_remainder_and_slack". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_holds_for_multiple_jobs". Abort.
Check @prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_holds_for_multiple_jobs.
Goal True. idtac "END|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_holds_for_multiple_jobs". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_bounds_interference". Abort.
Check @prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_bounds_interference.
Goal True. idtac "END|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_bounds_interference". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_monotonic". Abort.
Check @prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_monotonic.
Goal True. idtac "END|prosa.classic.analysis.global.jitter.interference_bound_edf.InterferenceBoundEDFJitter.interference_bound_edf_monotonic". Abort.
