(* Recomputes the authoritative `Check @name` fingerprints for classic/analysis/global/jitter/bertogna_fp_comp.v. *)
Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.classic.analysis.global.jitter.bertogna_fp_comp.
Require Import prosa.classic.analysis.global.jitter.bertogna_fp_theory.
Require Import prosa.classic.analysis.global.jitter.interference_bound.
Require Import prosa.classic.analysis.global.jitter.interference_bound_fp.
Require Import prosa.classic.analysis.global.jitter.workload_bound.
Require Import prosa.classic.model.arrival.basic.arrival_sequence.
Require Import prosa.classic.model.arrival.basic.job.
Require Import prosa.classic.model.arrival.basic.task.
Require Import prosa.classic.model.arrival.basic.task_arrival.
Require Import prosa.classic.model.priority.
Require Import prosa.classic.model.schedule.global.basic.interference.
Require Import prosa.classic.model.schedule.global.basic.schedule.
Require Import prosa.classic.model.schedule.global.jitter.constrained_deadlines.
Require Import prosa.classic.model.schedule.global.jitter.interference.
Require Import prosa.classic.model.schedule.global.jitter.job.
Require Import prosa.classic.model.schedule.global.jitter.platform.
Require Import prosa.classic.model.schedule.global.jitter.schedule.
Require Import prosa.classic.model.schedule.global.response_time.
Require Import prosa.classic.model.schedule.global.schedulability.
Require Import prosa.classic.model.schedule.global.workload.
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
Goal True. idtac "BEGIN|prosa.classic.analysis.global.jitter.bertogna_fp_comp.ResponseTimeIterationFP.per_task_rta". Abort.
Check @prosa.classic.analysis.global.jitter.bertogna_fp_comp.ResponseTimeIterationFP.per_task_rta.
Goal True. idtac "END|prosa.classic.analysis.global.jitter.bertogna_fp_comp.ResponseTimeIterationFP.per_task_rta". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.jitter.bertogna_fp_comp.ResponseTimeIterationFP.max_steps". Abort.
Check @prosa.classic.analysis.global.jitter.bertogna_fp_comp.ResponseTimeIterationFP.max_steps.
Goal True. idtac "END|prosa.classic.analysis.global.jitter.bertogna_fp_comp.ResponseTimeIterationFP.max_steps". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.jitter.bertogna_fp_comp.ResponseTimeIterationFP.fp_bound_of_task". Abort.
Check @prosa.classic.analysis.global.jitter.bertogna_fp_comp.ResponseTimeIterationFP.fp_bound_of_task.
Goal True. idtac "END|prosa.classic.analysis.global.jitter.bertogna_fp_comp.ResponseTimeIterationFP.fp_bound_of_task". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.jitter.bertogna_fp_comp.ResponseTimeIterationFP.fp_claimed_bounds". Abort.
Check @prosa.classic.analysis.global.jitter.bertogna_fp_comp.ResponseTimeIterationFP.fp_claimed_bounds.
Goal True. idtac "END|prosa.classic.analysis.global.jitter.bertogna_fp_comp.ResponseTimeIterationFP.fp_claimed_bounds". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.jitter.bertogna_fp_comp.ResponseTimeIterationFP.fp_schedulable". Abort.
Check @prosa.classic.analysis.global.jitter.bertogna_fp_comp.ResponseTimeIterationFP.fp_schedulable.
Goal True. idtac "END|prosa.classic.analysis.global.jitter.bertogna_fp_comp.ResponseTimeIterationFP.fp_schedulable". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.jitter.bertogna_fp_comp.ResponseTimeIterationFP.fp_claimed_bounds_unzip". Abort.
Check @prosa.classic.analysis.global.jitter.bertogna_fp_comp.ResponseTimeIterationFP.fp_claimed_bounds_unzip.
Goal True. idtac "END|prosa.classic.analysis.global.jitter.bertogna_fp_comp.ResponseTimeIterationFP.fp_claimed_bounds_unzip". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.jitter.bertogna_fp_comp.ResponseTimeIterationFP.fp_claimed_bounds_rcons". Abort.
Check @prosa.classic.analysis.global.jitter.bertogna_fp_comp.ResponseTimeIterationFP.fp_claimed_bounds_rcons.
Goal True. idtac "END|prosa.classic.analysis.global.jitter.bertogna_fp_comp.ResponseTimeIterationFP.fp_claimed_bounds_rcons". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.jitter.bertogna_fp_comp.ResponseTimeIterationFP.fp_claimed_bounds_take". Abort.
Check @prosa.classic.analysis.global.jitter.bertogna_fp_comp.ResponseTimeIterationFP.fp_claimed_bounds_take.
Goal True. idtac "END|prosa.classic.analysis.global.jitter.bertogna_fp_comp.ResponseTimeIterationFP.fp_claimed_bounds_take". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.jitter.bertogna_fp_comp.ResponseTimeIterationFP.fp_claimed_bounds_le_deadline". Abort.
Check @prosa.classic.analysis.global.jitter.bertogna_fp_comp.ResponseTimeIterationFP.fp_claimed_bounds_le_deadline.
Goal True. idtac "END|prosa.classic.analysis.global.jitter.bertogna_fp_comp.ResponseTimeIterationFP.fp_claimed_bounds_le_deadline". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.jitter.bertogna_fp_comp.ResponseTimeIterationFP.fp_claimed_bounds_ge_cost". Abort.
Check @prosa.classic.analysis.global.jitter.bertogna_fp_comp.ResponseTimeIterationFP.fp_claimed_bounds_ge_cost.
Goal True. idtac "END|prosa.classic.analysis.global.jitter.bertogna_fp_comp.ResponseTimeIterationFP.fp_claimed_bounds_ge_cost". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.jitter.bertogna_fp_comp.ResponseTimeIterationFP.per_task_rta_fold". Abort.
Check @prosa.classic.analysis.global.jitter.bertogna_fp_comp.ResponseTimeIterationFP.per_task_rta_fold.
Goal True. idtac "END|prosa.classic.analysis.global.jitter.bertogna_fp_comp.ResponseTimeIterationFP.per_task_rta_fold". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.jitter.bertogna_fp_comp.ResponseTimeIterationFP.fp_claimed_bounds_hp_tasks_have_smaller_index". Abort.
Check @prosa.classic.analysis.global.jitter.bertogna_fp_comp.ResponseTimeIterationFP.fp_claimed_bounds_hp_tasks_have_smaller_index.
Goal True. idtac "END|prosa.classic.analysis.global.jitter.bertogna_fp_comp.ResponseTimeIterationFP.fp_claimed_bounds_hp_tasks_have_smaller_index". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.jitter.bertogna_fp_comp.ResponseTimeIterationFP.bertogna_fp_comp_f_monotonic". Abort.
Check @prosa.classic.analysis.global.jitter.bertogna_fp_comp.ResponseTimeIterationFP.bertogna_fp_comp_f_monotonic.
Goal True. idtac "END|prosa.classic.analysis.global.jitter.bertogna_fp_comp.ResponseTimeIterationFP.bertogna_fp_comp_f_monotonic". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.jitter.bertogna_fp_comp.ResponseTimeIterationFP.bertogna_fp_comp_f_converges_early". Abort.
Check @prosa.classic.analysis.global.jitter.bertogna_fp_comp.ResponseTimeIterationFP.bertogna_fp_comp_f_converges_early.
Goal True. idtac "END|prosa.classic.analysis.global.jitter.bertogna_fp_comp.ResponseTimeIterationFP.bertogna_fp_comp_f_converges_early". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.jitter.bertogna_fp_comp.ResponseTimeIterationFP.bertogna_fp_comp_f_increases". Abort.
Check @prosa.classic.analysis.global.jitter.bertogna_fp_comp.ResponseTimeIterationFP.bertogna_fp_comp_f_increases.
Goal True. idtac "END|prosa.classic.analysis.global.jitter.bertogna_fp_comp.ResponseTimeIterationFP.bertogna_fp_comp_f_increases". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.jitter.bertogna_fp_comp.ResponseTimeIterationFP.bertogna_fp_comp_rt_grows_too_much". Abort.
Check @prosa.classic.analysis.global.jitter.bertogna_fp_comp.ResponseTimeIterationFP.bertogna_fp_comp_rt_grows_too_much.
Goal True. idtac "END|prosa.classic.analysis.global.jitter.bertogna_fp_comp.ResponseTimeIterationFP.bertogna_fp_comp_rt_grows_too_much". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.jitter.bertogna_fp_comp.ResponseTimeIterationFP.per_task_rta_converges". Abort.
Check @prosa.classic.analysis.global.jitter.bertogna_fp_comp.ResponseTimeIterationFP.per_task_rta_converges.
Goal True. idtac "END|prosa.classic.analysis.global.jitter.bertogna_fp_comp.ResponseTimeIterationFP.per_task_rta_converges". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.jitter.bertogna_fp_comp.ResponseTimeIterationFP.fp_analysis_yields_response_time_bounds". Abort.
Check @prosa.classic.analysis.global.jitter.bertogna_fp_comp.ResponseTimeIterationFP.fp_analysis_yields_response_time_bounds.
Goal True. idtac "END|prosa.classic.analysis.global.jitter.bertogna_fp_comp.ResponseTimeIterationFP.fp_analysis_yields_response_time_bounds". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.jitter.bertogna_fp_comp.ResponseTimeIterationFP.taskset_schedulable_by_fp_rta". Abort.
Check @prosa.classic.analysis.global.jitter.bertogna_fp_comp.ResponseTimeIterationFP.taskset_schedulable_by_fp_rta.
Goal True. idtac "END|prosa.classic.analysis.global.jitter.bertogna_fp_comp.ResponseTimeIterationFP.taskset_schedulable_by_fp_rta". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.global.jitter.bertogna_fp_comp.ResponseTimeIterationFP.jobs_schedulable_by_fp_rta". Abort.
Check @prosa.classic.analysis.global.jitter.bertogna_fp_comp.ResponseTimeIterationFP.jobs_schedulable_by_fp_rta.
Goal True. idtac "END|prosa.classic.analysis.global.jitter.bertogna_fp_comp.ResponseTimeIterationFP.jobs_schedulable_by_fp_rta". Abort.
