(* Recomputes the authoritative `Check @name` fingerprints for classic/analysis/uni/jitter/fp_rta_comp.v. *)
Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.classic.analysis.uni.jitter.fp_rta_comp.
Require Import prosa.classic.analysis.uni.jitter.fp_rta_theory.
Require Import prosa.classic.analysis.uni.jitter.workload_bound_fp.
Require Import prosa.classic.model.arrival.basic.arrival_sequence.
Require Import prosa.classic.model.arrival.basic.job.
Require Import prosa.classic.model.arrival.basic.task.
Require Import prosa.classic.model.arrival.basic.task_arrival.
Require Import prosa.classic.model.arrival.jitter.arrival_bounds.
Require Import prosa.classic.model.arrival.jitter.arrival_sequence.
Require Import prosa.classic.model.arrival.jitter.job.
Require Import prosa.classic.model.arrival.jitter.task_arrival.
Require Import prosa.classic.model.priority.
Require Import prosa.classic.model.schedule.uni.jitter.busy_interval.
Require Import prosa.classic.model.schedule.uni.jitter.platform.
Require Import prosa.classic.model.schedule.uni.jitter.schedule.
Require Import prosa.classic.model.schedule.uni.response_time.
Require Import prosa.classic.model.schedule.uni.schedulability.
Require Import prosa.classic.model.schedule.uni.schedule.
Require Import prosa.classic.model.schedule.uni.schedule_of_task.
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
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.jitter.fp_rta_comp.ResponseTimeIterationFP.max_steps". Abort.
Check @prosa.classic.analysis.uni.jitter.fp_rta_comp.ResponseTimeIterationFP.max_steps.
Goal True. idtac "END|prosa.classic.analysis.uni.jitter.fp_rta_comp.ResponseTimeIterationFP.max_steps". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.jitter.fp_rta_comp.ResponseTimeIterationFP.per_task_rta". Abort.
Check @prosa.classic.analysis.uni.jitter.fp_rta_comp.ResponseTimeIterationFP.per_task_rta.
Goal True. idtac "END|prosa.classic.analysis.uni.jitter.fp_rta_comp.ResponseTimeIterationFP.per_task_rta". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.jitter.fp_rta_comp.ResponseTimeIterationFP.fp_claimed_bounds". Abort.
Check @prosa.classic.analysis.uni.jitter.fp_rta_comp.ResponseTimeIterationFP.fp_claimed_bounds.
Goal True. idtac "END|prosa.classic.analysis.uni.jitter.fp_rta_comp.ResponseTimeIterationFP.fp_claimed_bounds". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.jitter.fp_rta_comp.ResponseTimeIterationFP.fp_schedulable". Abort.
Check @prosa.classic.analysis.uni.jitter.fp_rta_comp.ResponseTimeIterationFP.fp_schedulable.
Goal True. idtac "END|prosa.classic.analysis.uni.jitter.fp_rta_comp.ResponseTimeIterationFP.fp_schedulable". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.jitter.fp_rta_comp.ResponseTimeIterationFP.fp_claimed_bounds_for_every_task". Abort.
Check @prosa.classic.analysis.uni.jitter.fp_rta_comp.ResponseTimeIterationFP.fp_claimed_bounds_for_every_task.
Goal True. idtac "END|prosa.classic.analysis.uni.jitter.fp_rta_comp.ResponseTimeIterationFP.fp_claimed_bounds_for_every_task". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.jitter.fp_rta_comp.ResponseTimeIterationFP.fp_claimed_bounds_from_taskset". Abort.
Check @prosa.classic.analysis.uni.jitter.fp_rta_comp.ResponseTimeIterationFP.fp_claimed_bounds_from_taskset.
Goal True. idtac "END|prosa.classic.analysis.uni.jitter.fp_rta_comp.ResponseTimeIterationFP.fp_claimed_bounds_from_taskset". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.jitter.fp_rta_comp.ResponseTimeIterationFP.fp_claimed_bounds_computes_iteration". Abort.
Check @prosa.classic.analysis.uni.jitter.fp_rta_comp.ResponseTimeIterationFP.fp_claimed_bounds_computes_iteration.
Goal True. idtac "END|prosa.classic.analysis.uni.jitter.fp_rta_comp.ResponseTimeIterationFP.fp_claimed_bounds_computes_iteration". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.jitter.fp_rta_comp.ResponseTimeIterationFP.fp_claimed_bounds_yields_fixed_point". Abort.
Check @prosa.classic.analysis.uni.jitter.fp_rta_comp.ResponseTimeIterationFP.fp_claimed_bounds_yields_fixed_point.
Goal True. idtac "END|prosa.classic.analysis.uni.jitter.fp_rta_comp.ResponseTimeIterationFP.fp_claimed_bounds_yields_fixed_point". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.jitter.fp_rta_comp.ResponseTimeIterationFP.fp_claimed_bounds_le_deadline". Abort.
Check @prosa.classic.analysis.uni.jitter.fp_rta_comp.ResponseTimeIterationFP.fp_claimed_bounds_le_deadline.
Goal True. idtac "END|prosa.classic.analysis.uni.jitter.fp_rta_comp.ResponseTimeIterationFP.fp_claimed_bounds_le_deadline". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.jitter.fp_rta_comp.ResponseTimeIterationFP.fp_claimed_bounds_ge_cost". Abort.
Check @prosa.classic.analysis.uni.jitter.fp_rta_comp.ResponseTimeIterationFP.fp_claimed_bounds_ge_cost.
Goal True. idtac "END|prosa.classic.analysis.uni.jitter.fp_rta_comp.ResponseTimeIterationFP.fp_claimed_bounds_ge_cost". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.jitter.fp_rta_comp.ResponseTimeIterationFP.fp_claimed_bounds_gt_zero". Abort.
Check @prosa.classic.analysis.uni.jitter.fp_rta_comp.ResponseTimeIterationFP.fp_claimed_bounds_gt_zero.
Goal True. idtac "END|prosa.classic.analysis.uni.jitter.fp_rta_comp.ResponseTimeIterationFP.fp_claimed_bounds_gt_zero". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.jitter.fp_rta_comp.ResponseTimeIterationFP.fp_analysis_yields_response_time_bounds". Abort.
Check @prosa.classic.analysis.uni.jitter.fp_rta_comp.ResponseTimeIterationFP.fp_analysis_yields_response_time_bounds.
Goal True. idtac "END|prosa.classic.analysis.uni.jitter.fp_rta_comp.ResponseTimeIterationFP.fp_analysis_yields_response_time_bounds". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.jitter.fp_rta_comp.ResponseTimeIterationFP.taskset_schedulable_by_fp_rta". Abort.
Check @prosa.classic.analysis.uni.jitter.fp_rta_comp.ResponseTimeIterationFP.taskset_schedulable_by_fp_rta.
Goal True. idtac "END|prosa.classic.analysis.uni.jitter.fp_rta_comp.ResponseTimeIterationFP.taskset_schedulable_by_fp_rta". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.jitter.fp_rta_comp.ResponseTimeIterationFP.jobs_schedulable_by_fp_rta". Abort.
Check @prosa.classic.analysis.uni.jitter.fp_rta_comp.ResponseTimeIterationFP.jobs_schedulable_by_fp_rta.
Goal True. idtac "END|prosa.classic.analysis.uni.jitter.fp_rta_comp.ResponseTimeIterationFP.jobs_schedulable_by_fp_rta". Abort.
