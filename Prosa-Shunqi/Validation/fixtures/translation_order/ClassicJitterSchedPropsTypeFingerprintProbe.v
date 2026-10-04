(* Recomputes the authoritative `Check @name` fingerprints for classic/analysis/uni/susp/dynamic/jitter/jitter_schedule_properties.v. *)
Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule.
Require Import prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_properties.
Require Import prosa.classic.model.arrival.basic.arrival_sequence.
Require Import prosa.classic.model.arrival.basic.job.
Require Import prosa.classic.model.arrival.basic.task.
Require Import prosa.classic.model.arrival.basic.task_arrival.
Require Import prosa.classic.model.arrival.jitter.arrival_sequence.
Require Import prosa.classic.model.arrival.jitter.job.
Require Import prosa.classic.model.priority.
Require Import prosa.classic.model.schedule.uni.jitter.platform.
Require Import prosa.classic.model.schedule.uni.jitter.schedule.
Require Import prosa.classic.model.schedule.uni.jitter.valid_schedule.
Require Import prosa.classic.model.schedule.uni.response_time.
Require Import prosa.classic.model.schedule.uni.schedulability.
Require Import prosa.classic.model.schedule.uni.schedule.
Require Import prosa.classic.model.schedule.uni.service.
Require Import prosa.classic.model.schedule.uni.susp.last_execution.
Require Import prosa.classic.model.schedule.uni.susp.platform.
Require Import prosa.classic.model.schedule.uni.susp.schedule.
Require Import prosa.classic.model.schedule.uni.susp.suspension_intervals.
Require Import prosa.classic.model.schedule.uni.susp.valid_schedule.
Require Import prosa.classic.model.schedule.uni.transformation.construction.
Require Import prosa.classic.model.schedule.uni.workload.
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
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_properties.JitterScheduleProperties.sched_jitter_depends_only_on_service". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_properties.JitterScheduleProperties.sched_jitter_depends_only_on_service.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_properties.JitterScheduleProperties.sched_jitter_depends_only_on_service". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_properties.JitterScheduleProperties.sched_jitter_uses_construction_function". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_properties.JitterScheduleProperties.sched_jitter_uses_construction_function.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_properties.JitterScheduleProperties.sched_jitter_uses_construction_function". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_properties.JitterScheduleProperties.sched_jitter_jobs_come_from_arrival_sequence". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_properties.JitterScheduleProperties.sched_jitter_jobs_come_from_arrival_sequence.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_properties.JitterScheduleProperties.sched_jitter_jobs_come_from_arrival_sequence". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_properties.JitterScheduleProperties.sched_jitter_jobs_execute_after_jitter". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_properties.JitterScheduleProperties.sched_jitter_jobs_execute_after_jitter.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_properties.JitterScheduleProperties.sched_jitter_jobs_execute_after_jitter". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_properties.JitterScheduleProperties.sched_jitter_completed_jobs_dont_execute". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_properties.JitterScheduleProperties.sched_jitter_completed_jobs_dont_execute.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_properties.JitterScheduleProperties.sched_jitter_completed_jobs_dont_execute". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_properties.JitterScheduleProperties.sched_jitter_work_conserving". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_properties.JitterScheduleProperties.sched_jitter_work_conserving.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_properties.JitterScheduleProperties.sched_jitter_work_conserving". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_properties.JitterScheduleProperties.sched_jitter_respects_policy". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_properties.JitterScheduleProperties.sched_jitter_respects_policy.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_properties.JitterScheduleProperties.sched_jitter_respects_policy". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_properties.JitterScheduleProperties.sched_jitter_is_valid". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_properties.JitterScheduleProperties.sched_jitter_is_valid.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_properties.JitterScheduleProperties.sched_jitter_is_valid". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_properties.JitterScheduleProperties.sched_jitter_does_not_pick_j". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_properties.JitterScheduleProperties.sched_jitter_does_not_pick_j.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_properties.JitterScheduleProperties.sched_jitter_does_not_pick_j". Abort.
