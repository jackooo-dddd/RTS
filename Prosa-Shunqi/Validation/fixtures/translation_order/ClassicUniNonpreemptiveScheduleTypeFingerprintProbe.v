(* Recomputes the authoritative `Check @name` fingerprints for classic/model/schedule/uni/nonpreemptive/schedule.v. *)
Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.classic.model.arrival.basic.arrival_sequence.
Require Import prosa.classic.model.arrival.basic.job.
Require Import prosa.classic.model.arrival.basic.task.
Require Import prosa.classic.model.schedule.uni.nonpreemptive.schedule.
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
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.nonpreemptive.schedule.NonpreemptiveSchedule.is_nonpreemptive_schedule". Abort.
Check @prosa.classic.model.schedule.uni.nonpreemptive.schedule.NonpreemptiveSchedule.is_nonpreemptive_schedule.
Goal True. idtac "END|prosa.classic.model.schedule.uni.nonpreemptive.schedule.NonpreemptiveSchedule.is_nonpreemptive_schedule". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.nonpreemptive.schedule.NonpreemptiveSchedule.subh3". Abort.
Check @prosa.classic.model.schedule.uni.nonpreemptive.schedule.NonpreemptiveSchedule.subh3.
Goal True. idtac "END|prosa.classic.model.schedule.uni.nonpreemptive.schedule.NonpreemptiveSchedule.subh3". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.nonpreemptive.schedule.NonpreemptiveSchedule.continuity_of_nonpreemptive_scheduling". Abort.
Check @prosa.classic.model.schedule.uni.nonpreemptive.schedule.NonpreemptiveSchedule.continuity_of_nonpreemptive_scheduling.
Goal True. idtac "END|prosa.classic.model.schedule.uni.nonpreemptive.schedule.NonpreemptiveSchedule.continuity_of_nonpreemptive_scheduling". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.nonpreemptive.schedule.NonpreemptiveSchedule.in_nonpreemption_schedule_preemption_implies_completeness". Abort.
Check @prosa.classic.model.schedule.uni.nonpreemptive.schedule.NonpreemptiveSchedule.in_nonpreemption_schedule_preemption_implies_completeness.
Goal True. idtac "END|prosa.classic.model.schedule.uni.nonpreemptive.schedule.NonpreemptiveSchedule.in_nonpreemption_schedule_preemption_implies_completeness". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.nonpreemptive.schedule.NonpreemptiveSchedule.job_completes_after_remaining_cost". Abort.
Check @prosa.classic.model.schedule.uni.nonpreemptive.schedule.NonpreemptiveSchedule.job_completes_after_remaining_cost.
Goal True. idtac "END|prosa.classic.model.schedule.uni.nonpreemptive.schedule.NonpreemptiveSchedule.job_completes_after_remaining_cost". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.nonpreemptive.schedule.NonpreemptiveSchedule.j_is_scheduled_at_t_minus_service". Abort.
Check @prosa.classic.model.schedule.uni.nonpreemptive.schedule.NonpreemptiveSchedule.j_is_scheduled_at_t_minus_service.
Goal True. idtac "END|prosa.classic.model.schedule.uni.nonpreemptive.schedule.NonpreemptiveSchedule.j_is_scheduled_at_t_minus_service". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.nonpreemptive.schedule.NonpreemptiveSchedule.j_is_not_scheduled_at_t_minus_service_minus_one". Abort.
Check @prosa.classic.model.schedule.uni.nonpreemptive.schedule.NonpreemptiveSchedule.j_is_not_scheduled_at_t_minus_service_minus_one.
Goal True. idtac "END|prosa.classic.model.schedule.uni.nonpreemptive.schedule.NonpreemptiveSchedule.j_is_not_scheduled_at_t_minus_service_minus_one". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.nonpreemptive.schedule.NonpreemptiveSchedule.j_is_not_scheduled_earlier_t_minus_service". Abort.
Check @prosa.classic.model.schedule.uni.nonpreemptive.schedule.NonpreemptiveSchedule.j_is_not_scheduled_earlier_t_minus_service.
Goal True. idtac "END|prosa.classic.model.schedule.uni.nonpreemptive.schedule.NonpreemptiveSchedule.j_is_not_scheduled_earlier_t_minus_service". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.nonpreemptive.schedule.NonpreemptiveSchedule.j_is_scheduled_at_t_plus_remaining_cost_minus_one". Abort.
Check @prosa.classic.model.schedule.uni.nonpreemptive.schedule.NonpreemptiveSchedule.j_is_scheduled_at_t_plus_remaining_cost_minus_one.
Goal True. idtac "END|prosa.classic.model.schedule.uni.nonpreemptive.schedule.NonpreemptiveSchedule.j_is_scheduled_at_t_plus_remaining_cost_minus_one". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.nonpreemptive.schedule.NonpreemptiveSchedule.j_is_not_scheduled_after_t_plus_remaining_cost_minus_one". Abort.
Check @prosa.classic.model.schedule.uni.nonpreemptive.schedule.NonpreemptiveSchedule.j_is_not_scheduled_after_t_plus_remaining_cost_minus_one.
Goal True. idtac "END|prosa.classic.model.schedule.uni.nonpreemptive.schedule.NonpreemptiveSchedule.j_is_not_scheduled_after_t_plus_remaining_cost_minus_one". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.nonpreemptive.schedule.NonpreemptiveSchedule.nonpreemptive_executing_interval". Abort.
Check @prosa.classic.model.schedule.uni.nonpreemptive.schedule.NonpreemptiveSchedule.nonpreemptive_executing_interval.
Goal True. idtac "END|prosa.classic.model.schedule.uni.nonpreemptive.schedule.NonpreemptiveSchedule.nonpreemptive_executing_interval". Abort.
