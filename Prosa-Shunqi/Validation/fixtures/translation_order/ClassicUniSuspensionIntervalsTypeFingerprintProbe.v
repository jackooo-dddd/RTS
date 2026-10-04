(* Recomputes the authoritative `Check @name` fingerprints for classic/model/schedule/uni/susp/suspension_intervals.v. *)
Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.classic.model.arrival.basic.arrival_sequence.
Require Import prosa.classic.model.arrival.basic.job.
Require Import prosa.classic.model.arrival.basic.task.
Require Import prosa.classic.model.schedule.uni.schedule.
Require Import prosa.classic.model.schedule.uni.susp.last_execution.
Require Import prosa.classic.model.schedule.uni.susp.suspension_intervals.
Require Import prosa.classic.model.suspension.
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
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.susp.suspension_intervals.SuspensionIntervals.suspension_duration". Abort.
Check @prosa.classic.model.schedule.uni.susp.suspension_intervals.SuspensionIntervals.suspension_duration.
Goal True. idtac "END|prosa.classic.model.schedule.uni.susp.suspension_intervals.SuspensionIntervals.suspension_duration". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.susp.suspension_intervals.SuspensionIntervals.suspended_at". Abort.
Check @prosa.classic.model.schedule.uni.susp.suspension_intervals.SuspensionIntervals.suspended_at.
Goal True. idtac "END|prosa.classic.model.schedule.uni.susp.suspension_intervals.SuspensionIntervals.suspended_at". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.susp.suspension_intervals.SuspensionIntervals.cumulative_suspension_during". Abort.
Check @prosa.classic.model.schedule.uni.susp.suspension_intervals.SuspensionIntervals.cumulative_suspension_during.
Goal True. idtac "END|prosa.classic.model.schedule.uni.susp.suspension_intervals.SuspensionIntervals.cumulative_suspension_during". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.susp.suspension_intervals.SuspensionIntervals.cumulative_suspension". Abort.
Check @prosa.classic.model.schedule.uni.susp.suspension_intervals.SuspensionIntervals.cumulative_suspension.
Goal True. idtac "END|prosa.classic.model.schedule.uni.susp.suspension_intervals.SuspensionIntervals.cumulative_suspension". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.susp.suspension_intervals.SuspensionIntervals.respects_self_suspensions". Abort.
Check @prosa.classic.model.schedule.uni.susp.suspension_intervals.SuspensionIntervals.respects_self_suspensions.
Goal True. idtac "END|prosa.classic.model.schedule.uni.susp.suspension_intervals.SuspensionIntervals.respects_self_suspensions". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.susp.suspension_intervals.SuspensionIntervals.same_service_in_suspension_interval". Abort.
Check @prosa.classic.model.schedule.uni.susp.suspension_intervals.SuspensionIntervals.same_service_in_suspension_interval.
Goal True. idtac "END|prosa.classic.model.schedule.uni.susp.suspension_intervals.SuspensionIntervals.same_service_in_suspension_interval". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.susp.suspension_intervals.SuspensionIntervals.suspended_in_suspension_interval". Abort.
Check @prosa.classic.model.schedule.uni.susp.suspension_intervals.SuspensionIntervals.suspended_in_suspension_interval.
Goal True. idtac "END|prosa.classic.model.schedule.uni.susp.suspension_intervals.SuspensionIntervals.suspended_in_suspension_interval". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.susp.suspension_intervals.SuspensionIntervals.suspended_implies_arrived". Abort.
Check @prosa.classic.model.schedule.uni.susp.suspension_intervals.SuspensionIntervals.suspended_implies_arrived.
Goal True. idtac "END|prosa.classic.model.schedule.uni.susp.suspension_intervals.SuspensionIntervals.suspended_implies_arrived". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.susp.suspension_intervals.SuspensionIntervals.suspended_implies_not_completed". Abort.
Check @prosa.classic.model.schedule.uni.susp.suspension_intervals.SuspensionIntervals.suspended_implies_not_completed.
Goal True. idtac "END|prosa.classic.model.schedule.uni.susp.suspension_intervals.SuspensionIntervals.suspended_implies_not_completed". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.susp.suspension_intervals.SuspensionIntervals.cumulative_suspension_le_total_suspension". Abort.
Check @prosa.classic.model.schedule.uni.susp.suspension_intervals.SuspensionIntervals.cumulative_suspension_le_total_suspension.
Goal True. idtac "END|prosa.classic.model.schedule.uni.susp.suspension_intervals.SuspensionIntervals.cumulative_suspension_le_total_suspension". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.susp.suspension_intervals.SuspensionIntervals.cumulative_suspension_eq_total_suspension". Abort.
Check @prosa.classic.model.schedule.uni.susp.suspension_intervals.SuspensionIntervals.cumulative_suspension_eq_total_suspension.
Goal True. idtac "END|prosa.classic.model.schedule.uni.susp.suspension_intervals.SuspensionIntervals.cumulative_suspension_eq_total_suspension". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.susp.suspension_intervals.SuspensionIntervals.executes_before_suspension". Abort.
Check @prosa.classic.model.schedule.uni.susp.suspension_intervals.SuspensionIntervals.executes_before_suspension.
Goal True. idtac "END|prosa.classic.model.schedule.uni.susp.suspension_intervals.SuspensionIntervals.executes_before_suspension". Abort.
