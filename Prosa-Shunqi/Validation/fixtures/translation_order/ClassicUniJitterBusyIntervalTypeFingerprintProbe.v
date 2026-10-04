(* Recomputes the authoritative `Check @name` fingerprints for classic/model/schedule/uni/jitter/busy_interval.v. *)
Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.classic.model.arrival.basic.arrival_sequence.
Require Import prosa.classic.model.arrival.basic.job.
Require Import prosa.classic.model.arrival.basic.task.
Require Import prosa.classic.model.arrival.basic.task_arrival.
Require Import prosa.classic.model.arrival.jitter.arrival_sequence.
Require Import prosa.classic.model.priority.
Require Import prosa.classic.model.schedule.uni.jitter.busy_interval.
Require Import prosa.classic.model.schedule.uni.jitter.platform.
Require Import prosa.classic.model.schedule.uni.jitter.schedule.
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
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.jitter.busy_interval.BusyInterval.quiet_time". Abort.
Check @prosa.classic.model.schedule.uni.jitter.busy_interval.BusyInterval.quiet_time.
Goal True. idtac "END|prosa.classic.model.schedule.uni.jitter.busy_interval.BusyInterval.quiet_time". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.jitter.busy_interval.BusyInterval.busy_interval_prefix". Abort.
Check @prosa.classic.model.schedule.uni.jitter.busy_interval.BusyInterval.busy_interval_prefix.
Goal True. idtac "END|prosa.classic.model.schedule.uni.jitter.busy_interval.BusyInterval.busy_interval_prefix". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.jitter.busy_interval.BusyInterval.busy_interval". Abort.
Check @prosa.classic.model.schedule.uni.jitter.busy_interval.BusyInterval.busy_interval.
Goal True. idtac "END|prosa.classic.model.schedule.uni.jitter.busy_interval.BusyInterval.busy_interval". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.jitter.busy_interval.BusyInterval.job_completes_within_busy_interval". Abort.
Check @prosa.classic.model.schedule.uni.jitter.busy_interval.BusyInterval.job_completes_within_busy_interval.
Goal True. idtac "END|prosa.classic.model.schedule.uni.jitter.busy_interval.BusyInterval.job_completes_within_busy_interval". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.jitter.busy_interval.BusyInterval.job_arrives_within_busy_interval". Abort.
Check @prosa.classic.model.schedule.uni.jitter.busy_interval.BusyInterval.job_arrives_within_busy_interval.
Goal True. idtac "END|prosa.classic.model.schedule.uni.jitter.busy_interval.BusyInterval.job_arrives_within_busy_interval". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.jitter.busy_interval.BusyInterval.not_quiet_implies_exists_pending_job". Abort.
Check @prosa.classic.model.schedule.uni.jitter.busy_interval.BusyInterval.not_quiet_implies_exists_pending_job.
Goal True. idtac "END|prosa.classic.model.schedule.uni.jitter.busy_interval.BusyInterval.not_quiet_implies_exists_pending_job". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.jitter.busy_interval.BusyInterval.not_quiet_implies_not_idle". Abort.
Check @prosa.classic.model.schedule.uni.jitter.busy_interval.BusyInterval.not_quiet_implies_not_idle.
Goal True. idtac "END|prosa.classic.model.schedule.uni.jitter.busy_interval.BusyInterval.not_quiet_implies_not_idle". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.jitter.busy_interval.BusyInterval.not_quiet_implies_exists_scheduled_hp_job". Abort.
Check @prosa.classic.model.schedule.uni.jitter.busy_interval.BusyInterval.not_quiet_implies_exists_scheduled_hp_job.
Goal True. idtac "END|prosa.classic.model.schedule.uni.jitter.busy_interval.BusyInterval.not_quiet_implies_exists_scheduled_hp_job". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.jitter.busy_interval.BusyInterval.exists_busy_interval_prefix". Abort.
Check @prosa.classic.model.schedule.uni.jitter.busy_interval.BusyInterval.exists_busy_interval_prefix.
Goal True. idtac "END|prosa.classic.model.schedule.uni.jitter.busy_interval.BusyInterval.exists_busy_interval_prefix". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.jitter.busy_interval.BusyInterval.busy_interval_has_uninterrupted_service". Abort.
Check @prosa.classic.model.schedule.uni.jitter.busy_interval.BusyInterval.busy_interval_has_uninterrupted_service.
Goal True. idtac "END|prosa.classic.model.schedule.uni.jitter.busy_interval.BusyInterval.busy_interval_has_uninterrupted_service". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.jitter.busy_interval.BusyInterval.busy_interval_too_much_workload". Abort.
Check @prosa.classic.model.schedule.uni.jitter.busy_interval.BusyInterval.busy_interval_too_much_workload.
Goal True. idtac "END|prosa.classic.model.schedule.uni.jitter.busy_interval.BusyInterval.busy_interval_too_much_workload". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.jitter.busy_interval.BusyInterval.busy_interval_workload_larger_than_interval". Abort.
Check @prosa.classic.model.schedule.uni.jitter.busy_interval.BusyInterval.busy_interval_workload_larger_than_interval.
Goal True. idtac "END|prosa.classic.model.schedule.uni.jitter.busy_interval.BusyInterval.busy_interval_workload_larger_than_interval". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.jitter.busy_interval.BusyInterval.busy_interval_is_bounded". Abort.
Check @prosa.classic.model.schedule.uni.jitter.busy_interval.BusyInterval.busy_interval_is_bounded.
Goal True. idtac "END|prosa.classic.model.schedule.uni.jitter.busy_interval.BusyInterval.busy_interval_is_bounded". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.jitter.busy_interval.BusyInterval.exists_busy_interval". Abort.
Check @prosa.classic.model.schedule.uni.jitter.busy_interval.BusyInterval.exists_busy_interval.
Goal True. idtac "END|prosa.classic.model.schedule.uni.jitter.busy_interval.BusyInterval.exists_busy_interval". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.jitter.busy_interval.BusyInterval.busy_interval_bounds_response_time". Abort.
Check @prosa.classic.model.schedule.uni.jitter.busy_interval.BusyInterval.busy_interval_bounds_response_time.
Goal True. idtac "END|prosa.classic.model.schedule.uni.jitter.busy_interval.BusyInterval.busy_interval_bounds_response_time". Abort.
