(* Recomputes the authoritative `Check @name` fingerprints for classic/analysis/uni/basic/workload_bound_fp.v. *)
Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.classic.analysis.uni.basic.workload_bound_fp.
Require Import prosa.classic.model.arrival.basic.arrival_bounds.
Require Import prosa.classic.model.arrival.basic.arrival_sequence.
Require Import prosa.classic.model.arrival.basic.job.
Require Import prosa.classic.model.arrival.basic.task.
Require Import prosa.classic.model.arrival.basic.task_arrival.
Require Import prosa.classic.model.priority.
Require Import prosa.classic.model.schedule.uni.schedule.
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
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.basic.workload_bound_fp.WorkloadBoundFP.max_jobs". Abort.
Check @prosa.classic.analysis.uni.basic.workload_bound_fp.WorkloadBoundFP.max_jobs.
Goal True. idtac "END|prosa.classic.analysis.uni.basic.workload_bound_fp.WorkloadBoundFP.max_jobs". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.basic.workload_bound_fp.WorkloadBoundFP.task_workload_bound_FP". Abort.
Check @prosa.classic.analysis.uni.basic.workload_bound_fp.WorkloadBoundFP.task_workload_bound_FP.
Goal True. idtac "END|prosa.classic.analysis.uni.basic.workload_bound_fp.WorkloadBoundFP.task_workload_bound_FP". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.basic.workload_bound_fp.WorkloadBoundFP.total_workload_bound_fp". Abort.
Check @prosa.classic.analysis.uni.basic.workload_bound_fp.WorkloadBoundFP.total_workload_bound_fp.
Goal True. idtac "END|prosa.classic.analysis.uni.basic.workload_bound_fp.WorkloadBoundFP.total_workload_bound_fp". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.basic.workload_bound_fp.WorkloadBoundFP.total_workload_bound_fp_ge_cost". Abort.
Check @prosa.classic.analysis.uni.basic.workload_bound_fp.WorkloadBoundFP.total_workload_bound_fp_ge_cost.
Goal True. idtac "END|prosa.classic.analysis.uni.basic.workload_bound_fp.WorkloadBoundFP.total_workload_bound_fp_ge_cost". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.basic.workload_bound_fp.WorkloadBoundFP.total_workload_bound_fp_non_decreasing". Abort.
Check @prosa.classic.analysis.uni.basic.workload_bound_fp.WorkloadBoundFP.total_workload_bound_fp_non_decreasing.
Goal True. idtac "END|prosa.classic.analysis.uni.basic.workload_bound_fp.WorkloadBoundFP.total_workload_bound_fp_non_decreasing". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.basic.workload_bound_fp.WorkloadBoundFP.fp_workload_bound_holds". Abort.
Check @prosa.classic.analysis.uni.basic.workload_bound_fp.WorkloadBoundFP.fp_workload_bound_holds.
Goal True. idtac "END|prosa.classic.analysis.uni.basic.workload_bound_fp.WorkloadBoundFP.fp_workload_bound_holds". Abort.
