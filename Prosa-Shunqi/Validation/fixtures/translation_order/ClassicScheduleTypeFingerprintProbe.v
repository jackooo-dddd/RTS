(* Recomputes the authoritative `Check @name` fingerprints for classic/model/schedule/global/basic/schedule.v. *)
Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.classic.model.arrival.basic.arrival_sequence.
Require Import prosa.classic.model.arrival.basic.job.
Require Import prosa.classic.model.arrival.basic.task.
Require Import prosa.classic.model.schedule.global.basic.schedule.
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
Goal True. idtac "BEGIN|prosa.classic.model.schedule.global.basic.schedule.Schedule.processor". Abort.
Check @prosa.classic.model.schedule.global.basic.schedule.Schedule.processor.
Goal True. idtac "END|prosa.classic.model.schedule.global.basic.schedule.Schedule.processor". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.global.basic.schedule.Schedule.schedule". Abort.
Check @prosa.classic.model.schedule.global.basic.schedule.Schedule.schedule.
Goal True. idtac "END|prosa.classic.model.schedule.global.basic.schedule.Schedule.schedule". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.global.basic.schedule.Schedule.scheduled_on". Abort.
Check @prosa.classic.model.schedule.global.basic.schedule.Schedule.scheduled_on.
Goal True. idtac "END|prosa.classic.model.schedule.global.basic.schedule.Schedule.scheduled_on". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.global.basic.schedule.Schedule.scheduled". Abort.
Check @prosa.classic.model.schedule.global.basic.schedule.Schedule.scheduled.
Goal True. idtac "END|prosa.classic.model.schedule.global.basic.schedule.Schedule.scheduled". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.global.basic.schedule.Schedule.is_idle". Abort.
Check @prosa.classic.model.schedule.global.basic.schedule.Schedule.is_idle.
Goal True. idtac "END|prosa.classic.model.schedule.global.basic.schedule.Schedule.is_idle". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.global.basic.schedule.Schedule.service_at". Abort.
Check @prosa.classic.model.schedule.global.basic.schedule.Schedule.service_at.
Goal True. idtac "END|prosa.classic.model.schedule.global.basic.schedule.Schedule.service_at". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.global.basic.schedule.Schedule.service". Abort.
Check @prosa.classic.model.schedule.global.basic.schedule.Schedule.service.
Goal True. idtac "END|prosa.classic.model.schedule.global.basic.schedule.Schedule.service". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.global.basic.schedule.Schedule.service_during". Abort.
Check @prosa.classic.model.schedule.global.basic.schedule.Schedule.service_during.
Goal True. idtac "END|prosa.classic.model.schedule.global.basic.schedule.Schedule.service_during". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.global.basic.schedule.Schedule.completed". Abort.
Check @prosa.classic.model.schedule.global.basic.schedule.Schedule.completed.
Goal True. idtac "END|prosa.classic.model.schedule.global.basic.schedule.Schedule.completed". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.global.basic.schedule.Schedule.pending". Abort.
Check @prosa.classic.model.schedule.global.basic.schedule.Schedule.pending.
Goal True. idtac "END|prosa.classic.model.schedule.global.basic.schedule.Schedule.pending". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.global.basic.schedule.Schedule.backlogged". Abort.
Check @prosa.classic.model.schedule.global.basic.schedule.Schedule.backlogged.
Goal True. idtac "END|prosa.classic.model.schedule.global.basic.schedule.Schedule.backlogged". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.global.basic.schedule.Schedule.carried_in". Abort.
Check @prosa.classic.model.schedule.global.basic.schedule.Schedule.carried_in.
Goal True. idtac "END|prosa.classic.model.schedule.global.basic.schedule.Schedule.carried_in". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.global.basic.schedule.Schedule.carried_out". Abort.
Check @prosa.classic.model.schedule.global.basic.schedule.Schedule.carried_out.
Goal True. idtac "END|prosa.classic.model.schedule.global.basic.schedule.Schedule.carried_out". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.global.basic.schedule.Schedule.jobs_scheduled_at". Abort.
Check @prosa.classic.model.schedule.global.basic.schedule.Schedule.jobs_scheduled_at.
Goal True. idtac "END|prosa.classic.model.schedule.global.basic.schedule.Schedule.jobs_scheduled_at". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.global.basic.schedule.Schedule.jobs_scheduled_between". Abort.
Check @prosa.classic.model.schedule.global.basic.schedule.Schedule.jobs_scheduled_between.
Goal True. idtac "END|prosa.classic.model.schedule.global.basic.schedule.Schedule.jobs_scheduled_between". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.global.basic.schedule.Schedule.sequential_jobs". Abort.
Check @prosa.classic.model.schedule.global.basic.schedule.Schedule.sequential_jobs.
Goal True. idtac "END|prosa.classic.model.schedule.global.basic.schedule.Schedule.sequential_jobs". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.global.basic.schedule.Schedule.jobs_must_arrive_to_execute". Abort.
Check @prosa.classic.model.schedule.global.basic.schedule.Schedule.jobs_must_arrive_to_execute.
Goal True. idtac "END|prosa.classic.model.schedule.global.basic.schedule.Schedule.jobs_must_arrive_to_execute". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.global.basic.schedule.Schedule.completed_jobs_dont_execute". Abort.
Check @prosa.classic.model.schedule.global.basic.schedule.Schedule.completed_jobs_dont_execute.
Goal True. idtac "END|prosa.classic.model.schedule.global.basic.schedule.Schedule.completed_jobs_dont_execute". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.global.basic.schedule.Schedule.jobs_come_from_arrival_sequence". Abort.
Check @prosa.classic.model.schedule.global.basic.schedule.Schedule.jobs_come_from_arrival_sequence.
Goal True. idtac "END|prosa.classic.model.schedule.global.basic.schedule.Schedule.jobs_come_from_arrival_sequence". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.global.basic.schedule.Schedule.not_scheduled_no_service". Abort.
Check @prosa.classic.model.schedule.global.basic.schedule.Schedule.not_scheduled_no_service.
Goal True. idtac "END|prosa.classic.model.schedule.global.basic.schedule.Schedule.not_scheduled_no_service". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.global.basic.schedule.Schedule.cumulative_service_implies_service". Abort.
Check @prosa.classic.model.schedule.global.basic.schedule.Schedule.cumulative_service_implies_service.
Goal True. idtac "END|prosa.classic.model.schedule.global.basic.schedule.Schedule.cumulative_service_implies_service". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.global.basic.schedule.Schedule.service_implies_cumulative_service". Abort.
Check @prosa.classic.model.schedule.global.basic.schedule.Schedule.service_implies_cumulative_service.
Goal True. idtac "END|prosa.classic.model.schedule.global.basic.schedule.Schedule.service_implies_cumulative_service". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.global.basic.schedule.Schedule.service_at_most_one". Abort.
Check @prosa.classic.model.schedule.global.basic.schedule.Schedule.service_at_most_one.
Goal True. idtac "END|prosa.classic.model.schedule.global.basic.schedule.Schedule.service_at_most_one". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.global.basic.schedule.Schedule.cumulative_service_le_delta". Abort.
Check @prosa.classic.model.schedule.global.basic.schedule.Schedule.cumulative_service_le_delta.
Goal True. idtac "END|prosa.classic.model.schedule.global.basic.schedule.Schedule.cumulative_service_le_delta". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.global.basic.schedule.Schedule.completion_monotonic". Abort.
Check @prosa.classic.model.schedule.global.basic.schedule.Schedule.completion_monotonic.
Goal True. idtac "END|prosa.classic.model.schedule.global.basic.schedule.Schedule.completion_monotonic". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.global.basic.schedule.Schedule.completed_implies_not_scheduled". Abort.
Check @prosa.classic.model.schedule.global.basic.schedule.Schedule.completed_implies_not_scheduled.
Goal True. idtac "END|prosa.classic.model.schedule.global.basic.schedule.Schedule.completed_implies_not_scheduled". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.global.basic.schedule.Schedule.cumulative_service_le_job_cost". Abort.
Check @prosa.classic.model.schedule.global.basic.schedule.Schedule.cumulative_service_le_job_cost.
Goal True. idtac "END|prosa.classic.model.schedule.global.basic.schedule.Schedule.cumulative_service_le_job_cost". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.global.basic.schedule.Schedule.service_before_job_arrival_zero". Abort.
Check @prosa.classic.model.schedule.global.basic.schedule.Schedule.service_before_job_arrival_zero.
Goal True. idtac "END|prosa.classic.model.schedule.global.basic.schedule.Schedule.service_before_job_arrival_zero". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.global.basic.schedule.Schedule.cumulative_service_before_job_arrival_zero". Abort.
Check @prosa.classic.model.schedule.global.basic.schedule.Schedule.cumulative_service_before_job_arrival_zero.
Goal True. idtac "END|prosa.classic.model.schedule.global.basic.schedule.Schedule.cumulative_service_before_job_arrival_zero". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.global.basic.schedule.Schedule.service_before_arrival_eq_service_during". Abort.
Check @prosa.classic.model.schedule.global.basic.schedule.Schedule.service_before_arrival_eq_service_during.
Goal True. idtac "END|prosa.classic.model.schedule.global.basic.schedule.Schedule.service_before_arrival_eq_service_during". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.global.basic.schedule.Schedule.scheduled_implies_pending". Abort.
Check @prosa.classic.model.schedule.global.basic.schedule.Schedule.scheduled_implies_pending.
Goal True. idtac "END|prosa.classic.model.schedule.global.basic.schedule.Schedule.scheduled_implies_pending". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.global.basic.schedule.Schedule.mem_scheduled_jobs_eq_scheduled". Abort.
Check @prosa.classic.model.schedule.global.basic.schedule.Schedule.mem_scheduled_jobs_eq_scheduled.
Goal True. idtac "END|prosa.classic.model.schedule.global.basic.schedule.Schedule.mem_scheduled_jobs_eq_scheduled". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.global.basic.schedule.Schedule.scheduled_jobs_uniq". Abort.
Check @prosa.classic.model.schedule.global.basic.schedule.Schedule.scheduled_jobs_uniq.
Goal True. idtac "END|prosa.classic.model.schedule.global.basic.schedule.Schedule.scheduled_jobs_uniq". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.global.basic.schedule.Schedule.num_scheduled_jobs_le_num_cpus". Abort.
Check @prosa.classic.model.schedule.global.basic.schedule.Schedule.num_scheduled_jobs_le_num_cpus.
Goal True. idtac "END|prosa.classic.model.schedule.global.basic.schedule.Schedule.num_scheduled_jobs_le_num_cpus". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.global.basic.schedule.ScheduleOfSporadicTask.task_scheduled_on". Abort.
Check @prosa.classic.model.schedule.global.basic.schedule.ScheduleOfSporadicTask.task_scheduled_on.
Goal True. idtac "END|prosa.classic.model.schedule.global.basic.schedule.ScheduleOfSporadicTask.task_scheduled_on". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.global.basic.schedule.ScheduleOfSporadicTask.task_is_scheduled". Abort.
Check @prosa.classic.model.schedule.global.basic.schedule.ScheduleOfSporadicTask.task_is_scheduled.
Goal True. idtac "END|prosa.classic.model.schedule.global.basic.schedule.ScheduleOfSporadicTask.task_is_scheduled". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.global.basic.schedule.ScheduleOfSporadicTask.jobs_of_task_scheduled_between". Abort.
Check @prosa.classic.model.schedule.global.basic.schedule.ScheduleOfSporadicTask.jobs_of_task_scheduled_between.
Goal True. idtac "END|prosa.classic.model.schedule.global.basic.schedule.ScheduleOfSporadicTask.jobs_of_task_scheduled_between". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.global.basic.schedule.ScheduleOfSporadicTask.jobs_of_same_task_dont_execute_in_parallel". Abort.
Check @prosa.classic.model.schedule.global.basic.schedule.ScheduleOfSporadicTask.jobs_of_same_task_dont_execute_in_parallel.
Goal True. idtac "END|prosa.classic.model.schedule.global.basic.schedule.ScheduleOfSporadicTask.jobs_of_same_task_dont_execute_in_parallel". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.global.basic.schedule.ScheduleOfSporadicTask.cumulative_service_le_task_cost". Abort.
Check @prosa.classic.model.schedule.global.basic.schedule.ScheduleOfSporadicTask.cumulative_service_le_task_cost.
Goal True. idtac "END|prosa.classic.model.schedule.global.basic.schedule.ScheduleOfSporadicTask.cumulative_service_le_task_cost". Abort.
