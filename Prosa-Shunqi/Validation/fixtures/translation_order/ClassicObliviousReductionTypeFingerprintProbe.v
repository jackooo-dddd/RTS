(* Recomputes the authoritative `Check @name` fingerprints for classic/analysis/uni/susp/dynamic/oblivious/reduction.v. *)
Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.
Require Import prosa.classic.implementation.uni.basic.schedule.
Require Import prosa.classic.model.arrival.basic.arrival_sequence.
Require Import prosa.classic.model.arrival.basic.job.
Require Import prosa.classic.model.arrival.basic.task.
Require Import prosa.classic.model.arrival.basic.task_arrival.
Require Import prosa.classic.model.priority.
Require Import prosa.classic.model.schedule.uni.basic.platform.
Require Import prosa.classic.model.schedule.uni.response_time.
Require Import prosa.classic.model.schedule.uni.schedulability.
Require Import prosa.classic.model.schedule.uni.schedule.
Require Import prosa.classic.model.schedule.uni.susp.last_execution.
Require Import prosa.classic.model.schedule.uni.susp.platform.
Require Import prosa.classic.model.schedule.uni.susp.schedule.
Require Import prosa.classic.model.schedule.uni.susp.suspension_intervals.
Require Import prosa.classic.model.schedule.uni.transformation.construction.
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
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.inflated_job_cost". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.inflated_job_cost.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.inflated_job_cost". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.inflated_task_cost". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.inflated_task_cost.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.inflated_task_cost". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.suspension_oblivious_job_parameters_remain_valid". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.suspension_oblivious_job_parameters_remain_valid.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.suspension_oblivious_job_parameters_remain_valid". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.suspension_oblivious_task_parameters_remain_valid". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.suspension_oblivious_task_parameters_remain_valid.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.suspension_oblivious_task_parameters_remain_valid". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.pending_jobs". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.pending_jobs.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.pending_jobs". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.highest_priority_job". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.highest_priority_job.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.highest_priority_job". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.build_schedule". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.build_schedule.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.build_schedule". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.sched_new". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.sched_new.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.sched_new". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.sched_new_depends_only_on_service". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.sched_new_depends_only_on_service.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.sched_new_depends_only_on_service". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.sched_new_uses_construction_function". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.sched_new_uses_construction_function.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.sched_new_uses_construction_function". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.sched_newjobs_come_from_arrival_sequence". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.sched_newjobs_come_from_arrival_sequence.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.sched_newjobs_come_from_arrival_sequence". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.sched_new_jobs_must_arrive_to_execute". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.sched_new_jobs_must_arrive_to_execute.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.sched_new_jobs_must_arrive_to_execute". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.sched_new_completed_jobs_dont_execute". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.sched_new_completed_jobs_dont_execute.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.sched_new_completed_jobs_dont_execute". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.sched_new_work_conserving". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.sched_new_work_conserving.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.sched_new_work_conserving". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.sched_new_respects_policy". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.sched_new_respects_policy.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.sched_new_respects_policy". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.sched_new_breaks_ties". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.sched_new_breaks_ties.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.sched_new_breaks_ties". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.reduction_inductive_step_not_arrived". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.reduction_inductive_step_not_arrived.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.reduction_inductive_step_not_arrived". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.reduction_inductive_step_case1_completed". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.reduction_inductive_step_case1_completed.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.reduction_inductive_step_case1_completed". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.reduction_inductive_step_not_scheduled_in_new". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.reduction_inductive_step_not_scheduled_in_new.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.reduction_inductive_step_not_scheduled_in_new". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.reduction_inductive_step_scheduled_in_susp". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.reduction_inductive_step_scheduled_in_susp.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.reduction_inductive_step_scheduled_in_susp". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.reduction_inductive_step_j_is_backlogged". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.reduction_inductive_step_j_is_backlogged.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.reduction_inductive_step_j_is_backlogged". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.reduction_inductive_step_exists_hep_job". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.reduction_inductive_step_exists_hep_job.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.reduction_inductive_step_exists_hep_job". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.reduction_inductive_step_j_hp_completed_in_new". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.reduction_inductive_step_j_hp_completed_in_new.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.reduction_inductive_step_j_hp_completed_in_new". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.reduction_inductive_step_j_hp_completed_in_susp". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.reduction_inductive_step_j_hp_completed_in_susp.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.reduction_inductive_step_j_hp_completed_in_susp". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.reduction_inductive_step_contradiction". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.reduction_inductive_step_contradiction.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.reduction_inductive_step_contradiction". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.reduction_inductive_step_case2_pending". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.reduction_inductive_step_case2_pending.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.reduction_inductive_step_case2_pending". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.suspension_oblivious_preserves_service". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.suspension_oblivious_preserves_service.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.suspension_oblivious_preserves_service". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.suspension_oblivious_preserves_completion". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.suspension_oblivious_preserves_completion.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.suspension_oblivious_preserves_completion". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.suspension_oblivious_preserves_schedulability". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.suspension_oblivious_preserves_schedulability.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.oblivious.reduction.ReductionToBasicSchedule.suspension_oblivious_preserves_schedulability". Abort.
