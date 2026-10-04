(* Recomputes the authoritative `Check @name` fingerprints for classic/model/schedule/uni/limited/busy_interval.v. *)
Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.classic.model.arrival.basic.arrival_sequence.
Require Import prosa.classic.model.arrival.basic.job.
Require Import prosa.classic.model.arrival.basic.task.
Require Import prosa.classic.model.arrival.basic.task_arrival.
Require Import prosa.classic.model.priority.
Require Import prosa.classic.model.schedule.uni.basic.platform.
Require Import prosa.classic.model.schedule.uni.limited.busy_interval.
Require Import prosa.classic.model.schedule.uni.limited.platform.definitions.
Require Import prosa.classic.model.schedule.uni.nonpreemptive.schedule.
Require Import prosa.classic.model.schedule.uni.schedule.
Require Import prosa.classic.model.schedule.uni.service.
Require Import prosa.classic.model.schedule.uni.workload.
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
Require Import prosa.util.unit_growth.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop div path.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.quiet_time". Abort.
Check @prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.quiet_time.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.quiet_time". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.busy_interval_prefix". Abort.
Check @prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.busy_interval_prefix.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.busy_interval_prefix". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.busy_interval". Abort.
Check @prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.busy_interval.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.busy_interval". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.is_priority_inversion". Abort.
Check @prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.is_priority_inversion.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.is_priority_inversion". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.cumulative_priority_inversion". Abort.
Check @prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.cumulative_priority_inversion.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.cumulative_priority_inversion". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.priority_inversion_of_job_is_bounded_by". Abort.
Check @prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.priority_inversion_of_job_is_bounded_by.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.priority_inversion_of_job_is_bounded_by". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.priority_inversion_is_bounded_by". Abort.
Check @prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.priority_inversion_is_bounded_by.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.priority_inversion_is_bounded_by". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.quiet_time_dec". Abort.
Check @prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.quiet_time_dec.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.quiet_time_dec". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.quiet_time_P". Abort.
Check @prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.quiet_time_P.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.quiet_time_P". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.job_completes_within_busy_interval". Abort.
Check @prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.job_completes_within_busy_interval.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.job_completes_within_busy_interval". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.not_quiet_implies_exists_pending_job". Abort.
Check @prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.not_quiet_implies_exists_pending_job.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.not_quiet_implies_exists_pending_job". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.idle_time_implies_quiet_time_at_the_next_time_instant". Abort.
Check @prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.idle_time_implies_quiet_time_at_the_next_time_instant.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.idle_time_implies_quiet_time_at_the_next_time_instant". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.pending_hp_job_exists". Abort.
Check @prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.pending_hp_job_exists.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.pending_hp_job_exists". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.not_quiet_implies_not_idle". Abort.
Check @prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.not_quiet_implies_not_idle.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.not_quiet_implies_not_idle". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.hep_jobs_receive_no_service_before_quiet_time". Abort.
Check @prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.hep_jobs_receive_no_service_before_quiet_time.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.hep_jobs_receive_no_service_before_quiet_time". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.no_idle_time_within_non_quiet_time_interval". Abort.
Check @prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.no_idle_time_within_non_quiet_time_interval.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.no_idle_time_within_non_quiet_time_interval". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.exists_busy_interval_prefix". Abort.
Check @prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.exists_busy_interval_prefix.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.exists_busy_interval_prefix". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.busy_interval_has_uninterrupted_service". Abort.
Check @prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.busy_interval_has_uninterrupted_service.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.busy_interval_has_uninterrupted_service". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.busy_interval_too_much_workload". Abort.
Check @prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.busy_interval_too_much_workload.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.busy_interval_too_much_workload". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.busy_interval_workload_larger_than_interval". Abort.
Check @prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.busy_interval_workload_larger_than_interval.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.busy_interval_workload_larger_than_interval". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.busy_interval_is_bounded". Abort.
Check @prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.busy_interval_is_bounded.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.busy_interval_is_bounded". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.exists_busy_interval". Abort.
Check @prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.exists_busy_interval.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.exists_busy_interval". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.busy_interval_bounds_response_time". Abort.
Check @prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.busy_interval_bounds_response_time.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.busy_interval_bounds_response_time". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.no_carry_in". Abort.
Check @prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.no_carry_in.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.no_carry_in". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.no_carry_in_implies_quiet_time". Abort.
Check @prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.no_carry_in_implies_quiet_time.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.no_carry_in_implies_quiet_time". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.idle_instant_implies_no_carry_in_at_t". Abort.
Check @prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.idle_instant_implies_no_carry_in_at_t.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.idle_instant_implies_no_carry_in_at_t". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.idle_instant_implies_no_carry_in_at_t_pl_1". Abort.
Check @prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.idle_instant_implies_no_carry_in_at_t_pl_1.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.idle_instant_implies_no_carry_in_at_t_pl_1". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.no_carry_in_at_the_beginning". Abort.
Check @prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.no_carry_in_at_the_beginning.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.no_carry_in_at_the_beginning". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.total_service_is_bounded_by_Δ". Abort.
Check @prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.total_service_is_bounded_by_Δ.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.total_service_is_bounded_by_Δ". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.low_total_service_implies_existence_of_time_with_no_carry_in". Abort.
Check @prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.low_total_service_implies_existence_of_time_with_no_carry_in.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.low_total_service_implies_existence_of_time_with_no_carry_in". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.completion_of_all_jobs_implies_no_carry_in". Abort.
Check @prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.completion_of_all_jobs_implies_no_carry_in.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.completion_of_all_jobs_implies_no_carry_in". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.processor_is_not_too_busy". Abort.
Check @prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.processor_is_not_too_busy.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.processor_is_not_too_busy". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.exists_busy_interval_from_total_workload_bound". Abort.
Check @prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.exists_busy_interval_from_total_workload_bound.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.busy_interval.BusyIntervalJLFP.exists_busy_interval_from_total_workload_bound". Abort.
