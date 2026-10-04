(* Recomputes the authoritative `Check @name` fingerprints for classic/model/schedule/uni/schedule.v. *)
Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.classic.model.arrival.basic.arrival_sequence.
Require Import prosa.classic.model.arrival.basic.job.
Require Import prosa.classic.model.arrival.basic.task.
Require Import prosa.classic.model.schedule.uni.schedule.
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
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.schedule". Abort.
Check @prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.schedule.
Goal True. idtac "END|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.schedule". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.scheduled_at". Abort.
Check @prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.scheduled_at.
Goal True. idtac "END|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.scheduled_at". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.service_at". Abort.
Check @prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.service_at.
Goal True. idtac "END|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.service_at". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.service_during". Abort.
Check @prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.service_during.
Goal True. idtac "END|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.service_during". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.service". Abort.
Check @prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.service.
Goal True. idtac "END|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.service". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.completed_by". Abort.
Check @prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.completed_by.
Goal True. idtac "END|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.completed_by". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.pending". Abort.
Check @prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.pending.
Goal True. idtac "END|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.pending". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.pending_earlier_and_at". Abort.
Check @prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.pending_earlier_and_at.
Goal True. idtac "END|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.pending_earlier_and_at". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.backlogged". Abort.
Check @prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.backlogged.
Goal True. idtac "END|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.backlogged". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.is_idle". Abort.
Check @prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.is_idle.
Goal True. idtac "END|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.is_idle". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.total_service_during". Abort.
Check @prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.total_service_during.
Goal True. idtac "END|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.total_service_during". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.total_service". Abort.
Check @prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.total_service.
Goal True. idtac "END|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.total_service". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.sequential_jobs". Abort.
Check @prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.sequential_jobs.
Goal True. idtac "END|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.sequential_jobs". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.scheduler_executes_job_with_earliest_arrival". Abort.
Check @prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.scheduler_executes_job_with_earliest_arrival.
Goal True. idtac "END|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.scheduler_executes_job_with_earliest_arrival". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.jobs_come_from_arrival_sequence". Abort.
Check @prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.jobs_come_from_arrival_sequence.
Goal True. idtac "END|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.jobs_come_from_arrival_sequence". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.jobs_must_arrive_to_execute". Abort.
Check @prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.jobs_must_arrive_to_execute.
Goal True. idtac "END|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.jobs_must_arrive_to_execute". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.completed_jobs_dont_execute". Abort.
Check @prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.completed_jobs_dont_execute.
Goal True. idtac "END|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.completed_jobs_dont_execute". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.remaining_cost". Abort.
Check @prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.remaining_cost.
Goal True. idtac "END|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.remaining_cost". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.service_at_most_one". Abort.
Check @prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.service_at_most_one.
Goal True. idtac "END|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.service_at_most_one". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.cumulative_service_le_delta". Abort.
Check @prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.cumulative_service_le_delta.
Goal True. idtac "END|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.cumulative_service_le_delta". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.scheduled_implies_positive_remaining_cost". Abort.
Check @prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.scheduled_implies_positive_remaining_cost.
Goal True. idtac "END|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.scheduled_implies_positive_remaining_cost". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.completion_monotonic". Abort.
Check @prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.completion_monotonic.
Goal True. idtac "END|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.completion_monotonic". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.completed_implies_not_scheduled". Abort.
Check @prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.completed_implies_not_scheduled.
Goal True. idtac "END|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.completed_implies_not_scheduled". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.scheduled_implies_not_completed". Abort.
Check @prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.scheduled_implies_not_completed.
Goal True. idtac "END|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.scheduled_implies_not_completed". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.cumulative_service_le_job_cost". Abort.
Check @prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.cumulative_service_le_job_cost.
Goal True. idtac "END|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.cumulative_service_le_job_cost". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.job_doesnt_complete_before_remaining_cost". Abort.
Check @prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.job_doesnt_complete_before_remaining_cost.
Goal True. idtac "END|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.job_doesnt_complete_before_remaining_cost". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.completed_implies_scheduled_before". Abort.
Check @prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.completed_implies_scheduled_before.
Goal True. idtac "END|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.completed_implies_scheduled_before". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.service_before_job_arrival_zero". Abort.
Check @prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.service_before_job_arrival_zero.
Goal True. idtac "END|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.service_before_job_arrival_zero". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.cumulative_service_before_job_arrival_zero". Abort.
Check @prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.cumulative_service_before_job_arrival_zero.
Goal True. idtac "END|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.cumulative_service_before_job_arrival_zero". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.ignore_service_before_arrival". Abort.
Check @prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.ignore_service_before_arrival.
Goal True. idtac "END|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.ignore_service_before_arrival". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.scheduled_implies_pending". Abort.
Check @prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.scheduled_implies_pending.
Goal True. idtac "END|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.scheduled_implies_pending". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.job_pending_at_arrival". Abort.
Check @prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.job_pending_at_arrival.
Goal True. idtac "END|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.job_pending_at_arrival". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.only_one_job_scheduled". Abort.
Check @prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.only_one_job_scheduled.
Goal True. idtac "END|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.only_one_job_scheduled". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.service_is_a_step_function". Abort.
Check @prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.service_is_a_step_function.
Goal True. idtac "END|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.service_is_a_step_function". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.exists_intermediate_service". Abort.
Check @prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.exists_intermediate_service.
Goal True. idtac "END|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.exists_intermediate_service". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.scheduled_at_earlier_time". Abort.
Check @prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.scheduled_at_earlier_time.
Goal True. idtac "END|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.scheduled_at_earlier_time". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.cumulative_service_implies_scheduled". Abort.
Check @prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.cumulative_service_implies_scheduled.
Goal True. idtac "END|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.cumulative_service_implies_scheduled". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.same_service_implies_scheduled_at_earlier_times". Abort.
Check @prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.same_service_implies_scheduled_at_earlier_times.
Goal True. idtac "END|prosa.classic.model.schedule.uni.schedule.UniprocessorSchedule.same_service_implies_scheduled_at_earlier_times". Abort.
