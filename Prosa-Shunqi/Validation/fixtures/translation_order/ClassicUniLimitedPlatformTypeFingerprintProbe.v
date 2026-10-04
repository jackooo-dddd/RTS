(* Recomputes the authoritative `Check @name` fingerprints for classic/model/schedule/uni/limited/platform/definitions.v. *)
Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.classic.model.arrival.basic.arrival_sequence.
Require Import prosa.classic.model.arrival.basic.job.
Require Import prosa.classic.model.arrival.basic.task.
Require Import prosa.classic.model.arrival.basic.task_arrival.
Require Import prosa.classic.model.priority.
Require Import prosa.classic.model.schedule.uni.basic.platform.
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
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.platform.definitions.LimitedPreemptionPlatform.preemption_time". Abort.
Check @prosa.classic.model.schedule.uni.limited.platform.definitions.LimitedPreemptionPlatform.preemption_time.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.platform.definitions.LimitedPreemptionPlatform.preemption_time". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.platform.definitions.LimitedPreemptionPlatform.not_preemptive_implies_scheduled". Abort.
Check @prosa.classic.model.schedule.uni.limited.platform.definitions.LimitedPreemptionPlatform.not_preemptive_implies_scheduled.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.platform.definitions.LimitedPreemptionPlatform.not_preemptive_implies_scheduled". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.platform.definitions.LimitedPreemptionPlatform.execution_starts_with_preemption_point". Abort.
Check @prosa.classic.model.schedule.uni.limited.platform.definitions.LimitedPreemptionPlatform.execution_starts_with_preemption_point.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.platform.definitions.LimitedPreemptionPlatform.execution_starts_with_preemption_point". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.platform.definitions.LimitedPreemptionPlatform.correct_preemption_model". Abort.
Check @prosa.classic.model.schedule.uni.limited.platform.definitions.LimitedPreemptionPlatform.correct_preemption_model.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.platform.definitions.LimitedPreemptionPlatform.correct_preemption_model". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.platform.definitions.LimitedPreemptionPlatform.job_cannot_become_nonpreemptive_before_execution". Abort.
Check @prosa.classic.model.schedule.uni.limited.platform.definitions.LimitedPreemptionPlatform.job_cannot_become_nonpreemptive_before_execution.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.platform.definitions.LimitedPreemptionPlatform.job_cannot_become_nonpreemptive_before_execution". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.platform.definitions.LimitedPreemptionPlatform.job_cannot_be_nonpreemptive_after_completion". Abort.
Check @prosa.classic.model.schedule.uni.limited.platform.definitions.LimitedPreemptionPlatform.job_cannot_be_nonpreemptive_after_completion.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.platform.definitions.LimitedPreemptionPlatform.job_cannot_be_nonpreemptive_after_completion". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.platform.definitions.LimitedPreemptionPlatform.job_max_nonpreemptive_segment_le_task_max_nonpreemptive_segment". Abort.
Check @prosa.classic.model.schedule.uni.limited.platform.definitions.LimitedPreemptionPlatform.job_max_nonpreemptive_segment_le_task_max_nonpreemptive_segment.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.platform.definitions.LimitedPreemptionPlatform.job_max_nonpreemptive_segment_le_task_max_nonpreemptive_segment". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.platform.definitions.LimitedPreemptionPlatform.nonpreemptive_regions_have_bounded_length". Abort.
Check @prosa.classic.model.schedule.uni.limited.platform.definitions.LimitedPreemptionPlatform.nonpreemptive_regions_have_bounded_length.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.platform.definitions.LimitedPreemptionPlatform.nonpreemptive_regions_have_bounded_length". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.platform.definitions.LimitedPreemptionPlatform.model_with_bounded_nonpreemptive_segments". Abort.
Check @prosa.classic.model.schedule.uni.limited.platform.definitions.LimitedPreemptionPlatform.model_with_bounded_nonpreemptive_segments.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.platform.definitions.LimitedPreemptionPlatform.model_with_bounded_nonpreemptive_segments". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.platform.definitions.LimitedPreemptionPlatform.zero_is_pt". Abort.
Check @prosa.classic.model.schedule.uni.limited.platform.definitions.LimitedPreemptionPlatform.zero_is_pt.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.platform.definitions.LimitedPreemptionPlatform.zero_is_pt". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.platform.definitions.LimitedPreemptionPlatform.first_moment_is_pt". Abort.
Check @prosa.classic.model.schedule.uni.limited.platform.definitions.LimitedPreemptionPlatform.first_moment_is_pt.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.platform.definitions.LimitedPreemptionPlatform.first_moment_is_pt". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.platform.definitions.LimitedPreemptionPlatform.work_conserving". Abort.
Check @prosa.classic.model.schedule.uni.limited.platform.definitions.LimitedPreemptionPlatform.work_conserving.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.platform.definitions.LimitedPreemptionPlatform.work_conserving". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.platform.definitions.LimitedPreemptionPlatform.respects_FP_policy_at_preemption_point". Abort.
Check @prosa.classic.model.schedule.uni.limited.platform.definitions.LimitedPreemptionPlatform.respects_FP_policy_at_preemption_point.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.platform.definitions.LimitedPreemptionPlatform.respects_FP_policy_at_preemption_point". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.platform.definitions.LimitedPreemptionPlatform.respects_JLFP_policy_at_preemption_point". Abort.
Check @prosa.classic.model.schedule.uni.limited.platform.definitions.LimitedPreemptionPlatform.respects_JLFP_policy_at_preemption_point.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.platform.definitions.LimitedPreemptionPlatform.respects_JLFP_policy_at_preemption_point". Abort.
