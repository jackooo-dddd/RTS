(* Recomputes the authoritative `Check @name` fingerprints for classic/analysis/global/basic/workload_bound.v. *)
Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.classic.analysis.global.basic.workload_bound.
Require Import prosa.classic.model.arrival.basic.arrival_sequence.
Require Import prosa.classic.model.arrival.basic.job.
Require Import prosa.classic.model.arrival.basic.task.
Require Import prosa.classic.model.arrival.basic.task_arrival.
Require Import prosa.classic.model.schedule.global.basic.schedule.
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
Goal True. idtac "BEGIN|prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.max_jobs". Abort.
Check @prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.max_jobs.
Goal True. idtac "END|prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.max_jobs". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.W". Abort.
Check @prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.W.
Goal True. idtac "END|prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.W". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.W_monotonic". Abort.
Check @prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.W_monotonic.
Goal True. idtac "END|prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.W_monotonic". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.workload_bound_simpl_by_sorting_scheduled_jobs". Abort.
Check @prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.workload_bound_simpl_by_sorting_scheduled_jobs.
Goal True. idtac "END|prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.workload_bound_simpl_by_sorting_scheduled_jobs". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.workload_bound_job_in_same_sequence". Abort.
Check @prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.workload_bound_job_in_same_sequence.
Goal True. idtac "END|prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.workload_bound_job_in_same_sequence". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.workload_bound_all_jobs_from_tsk". Abort.
Check @prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.workload_bound_all_jobs_from_tsk.
Goal True. idtac "END|prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.workload_bound_all_jobs_from_tsk". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.workload_bound_jobs_ordered_by_arrival". Abort.
Check @prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.workload_bound_jobs_ordered_by_arrival.
Goal True. idtac "END|prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.workload_bound_jobs_ordered_by_arrival". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.workload_bound_holds_for_at_most_n_k_jobs". Abort.
Check @prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.workload_bound_holds_for_at_most_n_k_jobs.
Goal True. idtac "END|prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.workload_bound_holds_for_at_most_n_k_jobs". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.workload_bound_j_fst_is_job_of_tsk". Abort.
Check @prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.workload_bound_j_fst_is_job_of_tsk.
Goal True. idtac "END|prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.workload_bound_j_fst_is_job_of_tsk". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.workload_bound_holds_for_a_single_job". Abort.
Check @prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.workload_bound_holds_for_a_single_job.
Goal True. idtac "END|prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.workload_bound_holds_for_a_single_job". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.workload_bound_j_lst_is_job_of_tsk". Abort.
Check @prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.workload_bound_j_lst_is_job_of_tsk.
Goal True. idtac "END|prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.workload_bound_j_lst_is_job_of_tsk". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.workload_bound_response_time_of_first_job_inside_interval". Abort.
Check @prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.workload_bound_response_time_of_first_job_inside_interval.
Goal True. idtac "END|prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.workload_bound_response_time_of_first_job_inside_interval". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.workload_bound_last_job_arrives_before_end_of_interval". Abort.
Check @prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.workload_bound_last_job_arrives_before_end_of_interval.
Goal True. idtac "END|prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.workload_bound_last_job_arrives_before_end_of_interval". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.workload_bound_service_of_first_and_last_jobs". Abort.
Check @prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.workload_bound_service_of_first_and_last_jobs.
Goal True. idtac "END|prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.workload_bound_service_of_first_and_last_jobs". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.workload_bound_simpl_expression_with_first_and_last". Abort.
Check @prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.workload_bound_simpl_expression_with_first_and_last.
Goal True. idtac "END|prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.workload_bound_simpl_expression_with_first_and_last". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.workload_bound_service_of_middle_jobs". Abort.
Check @prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.workload_bound_service_of_middle_jobs.
Goal True. idtac "END|prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.workload_bound_service_of_middle_jobs". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.workload_bound_many_periods_in_between". Abort.
Check @prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.workload_bound_many_periods_in_between.
Goal True. idtac "END|prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.workload_bound_many_periods_in_between". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.workload_bound_n_k_covers_middle_jobs". Abort.
Check @prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.workload_bound_n_k_covers_middle_jobs.
Goal True. idtac "END|prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.workload_bound_n_k_covers_middle_jobs". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.workload_bound_n_k_equals_num_mid_jobs". Abort.
Check @prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.workload_bound_n_k_equals_num_mid_jobs.
Goal True. idtac "END|prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.workload_bound_n_k_equals_num_mid_jobs". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.workload_bound_n_k_equals_num_mid_jobs_plus_1". Abort.
Check @prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.workload_bound_n_k_equals_num_mid_jobs_plus_1.
Goal True. idtac "END|prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.workload_bound_n_k_equals_num_mid_jobs_plus_1". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.workload_bounded_by_W". Abort.
Check @prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.workload_bounded_by_W.
Goal True. idtac "END|prosa.classic.analysis.global.basic.workload_bound.WorkloadBound.workload_bounded_by_W". Abort.
