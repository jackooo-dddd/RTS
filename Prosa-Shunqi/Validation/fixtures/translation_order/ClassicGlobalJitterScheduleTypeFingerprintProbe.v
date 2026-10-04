(* Recomputes the authoritative `Check @name` fingerprints for classic/model/schedule/global/jitter/schedule.v. *)
Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.classic.model.arrival.basic.arrival_sequence.
Require Import prosa.classic.model.arrival.basic.job.
Require Import prosa.classic.model.arrival.basic.task.
Require Import prosa.classic.model.schedule.global.basic.schedule.
Require Import prosa.classic.model.schedule.global.jitter.job.
Require Import prosa.classic.model.schedule.global.jitter.schedule.
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
Goal True. idtac "BEGIN|prosa.classic.model.schedule.global.jitter.schedule.ScheduleWithJitter.actual_arrival". Abort.
Check @prosa.classic.model.schedule.global.jitter.schedule.ScheduleWithJitter.actual_arrival.
Goal True. idtac "END|prosa.classic.model.schedule.global.jitter.schedule.ScheduleWithJitter.actual_arrival". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.global.jitter.schedule.ScheduleWithJitter.jitter_has_passed". Abort.
Check @prosa.classic.model.schedule.global.jitter.schedule.ScheduleWithJitter.jitter_has_passed.
Goal True. idtac "END|prosa.classic.model.schedule.global.jitter.schedule.ScheduleWithJitter.jitter_has_passed". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.global.jitter.schedule.ScheduleWithJitter.actual_arrival_before". Abort.
Check @prosa.classic.model.schedule.global.jitter.schedule.ScheduleWithJitter.actual_arrival_before.
Goal True. idtac "END|prosa.classic.model.schedule.global.jitter.schedule.ScheduleWithJitter.actual_arrival_before". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.global.jitter.schedule.ScheduleWithJitter.pending". Abort.
Check @prosa.classic.model.schedule.global.jitter.schedule.ScheduleWithJitter.pending.
Goal True. idtac "END|prosa.classic.model.schedule.global.jitter.schedule.ScheduleWithJitter.pending". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.global.jitter.schedule.ScheduleWithJitter.backlogged". Abort.
Check @prosa.classic.model.schedule.global.jitter.schedule.ScheduleWithJitter.backlogged.
Goal True. idtac "END|prosa.classic.model.schedule.global.jitter.schedule.ScheduleWithJitter.backlogged". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.global.jitter.schedule.ScheduleWithJitter.jobs_execute_after_jitter". Abort.
Check @prosa.classic.model.schedule.global.jitter.schedule.ScheduleWithJitter.jobs_execute_after_jitter.
Goal True. idtac "END|prosa.classic.model.schedule.global.jitter.schedule.ScheduleWithJitter.jobs_execute_after_jitter". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.global.jitter.schedule.ScheduleWithJitter.scheduled_implies_pending". Abort.
Check @prosa.classic.model.schedule.global.jitter.schedule.ScheduleWithJitter.scheduled_implies_pending.
Goal True. idtac "END|prosa.classic.model.schedule.global.jitter.schedule.ScheduleWithJitter.scheduled_implies_pending". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.global.jitter.schedule.ScheduleWithJitter.arrival_before_jitter". Abort.
Check @prosa.classic.model.schedule.global.jitter.schedule.ScheduleWithJitter.arrival_before_jitter.
Goal True. idtac "END|prosa.classic.model.schedule.global.jitter.schedule.ScheduleWithJitter.arrival_before_jitter". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.global.jitter.schedule.ScheduleWithJitter.service_before_jitter_zero". Abort.
Check @prosa.classic.model.schedule.global.jitter.schedule.ScheduleWithJitter.service_before_jitter_zero.
Goal True. idtac "END|prosa.classic.model.schedule.global.jitter.schedule.ScheduleWithJitter.service_before_jitter_zero". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.global.jitter.schedule.ScheduleWithJitter.cumulative_service_before_jitter_zero". Abort.
Check @prosa.classic.model.schedule.global.jitter.schedule.ScheduleWithJitter.cumulative_service_before_jitter_zero.
Goal True. idtac "END|prosa.classic.model.schedule.global.jitter.schedule.ScheduleWithJitter.cumulative_service_before_jitter_zero". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.global.jitter.schedule.ScheduleOfSporadicTaskWithJitter.task_scheduled_on". Abort.
Check @prosa.classic.model.schedule.global.jitter.schedule.ScheduleOfSporadicTaskWithJitter.task_scheduled_on.
Goal True. idtac "END|prosa.classic.model.schedule.global.jitter.schedule.ScheduleOfSporadicTaskWithJitter.task_scheduled_on". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.global.jitter.schedule.ScheduleOfSporadicTaskWithJitter.task_is_scheduled". Abort.
Check @prosa.classic.model.schedule.global.jitter.schedule.ScheduleOfSporadicTaskWithJitter.task_is_scheduled.
Goal True. idtac "END|prosa.classic.model.schedule.global.jitter.schedule.ScheduleOfSporadicTaskWithJitter.task_is_scheduled". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.global.jitter.schedule.ScheduleOfSporadicTaskWithJitter.jobs_of_task_scheduled_between". Abort.
Check @prosa.classic.model.schedule.global.jitter.schedule.ScheduleOfSporadicTaskWithJitter.jobs_of_task_scheduled_between.
Goal True. idtac "END|prosa.classic.model.schedule.global.jitter.schedule.ScheduleOfSporadicTaskWithJitter.jobs_of_task_scheduled_between". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.global.jitter.schedule.ScheduleOfSporadicTaskWithJitter.jobs_of_same_task_dont_execute_in_parallel". Abort.
Check @prosa.classic.model.schedule.global.jitter.schedule.ScheduleOfSporadicTaskWithJitter.jobs_of_same_task_dont_execute_in_parallel.
Goal True. idtac "END|prosa.classic.model.schedule.global.jitter.schedule.ScheduleOfSporadicTaskWithJitter.jobs_of_same_task_dont_execute_in_parallel". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.global.jitter.schedule.ScheduleOfSporadicTaskWithJitter.cumulative_service_le_task_cost". Abort.
Check @prosa.classic.model.schedule.global.jitter.schedule.ScheduleOfSporadicTaskWithJitter.cumulative_service_le_task_cost.
Goal True. idtac "END|prosa.classic.model.schedule.global.jitter.schedule.ScheduleOfSporadicTaskWithJitter.cumulative_service_le_task_cost". Abort.
