(* Recomputes the authoritative `Check @name` fingerprints for classic/model/priority.v. *)
Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.classic.model.arrival.basic.arrival_sequence.
Require Import prosa.classic.model.arrival.basic.job.
Require Import prosa.classic.model.arrival.basic.task.
Require Import prosa.classic.model.priority.
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
Goal True. idtac "BEGIN|prosa.classic.model.priority.Priority.FP_policy". Abort.
Check @prosa.classic.model.priority.Priority.FP_policy.
Goal True. idtac "END|prosa.classic.model.priority.Priority.FP_policy". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.priority.Priority.JLFP_policy". Abort.
Check @prosa.classic.model.priority.Priority.JLFP_policy.
Goal True. idtac "END|prosa.classic.model.priority.Priority.JLFP_policy". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.priority.Priority.JLDP_policy". Abort.
Check @prosa.classic.model.priority.Priority.JLDP_policy.
Goal True. idtac "END|prosa.classic.model.priority.Priority.JLDP_policy". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.priority.Priority.FP_to_JLFP". Abort.
Check @prosa.classic.model.priority.Priority.FP_to_JLFP.
Goal True. idtac "END|prosa.classic.model.priority.Priority.FP_to_JLFP". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.priority.Priority.FP_to_JLDP". Abort.
Check @prosa.classic.model.priority.Priority.FP_to_JLDP.
Goal True. idtac "END|prosa.classic.model.priority.Priority.FP_to_JLDP". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.priority.Priority.JLFP_to_JLDP". Abort.
Check @prosa.classic.model.priority.Priority.JLFP_to_JLDP.
Goal True. idtac "END|prosa.classic.model.priority.Priority.JLFP_to_JLDP". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.priority.Priority.FP_is_reflexive". Abort.
Check @prosa.classic.model.priority.Priority.FP_is_reflexive.
Goal True. idtac "END|prosa.classic.model.priority.Priority.FP_is_reflexive". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.priority.Priority.FP_is_irreflexive". Abort.
Check @prosa.classic.model.priority.Priority.FP_is_irreflexive.
Goal True. idtac "END|prosa.classic.model.priority.Priority.FP_is_irreflexive". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.priority.Priority.FP_is_transitive". Abort.
Check @prosa.classic.model.priority.Priority.FP_is_transitive.
Goal True. idtac "END|prosa.classic.model.priority.Priority.FP_is_transitive". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.priority.Priority.FP_is_total_over_task_set". Abort.
Check @prosa.classic.model.priority.Priority.FP_is_total_over_task_set.
Goal True. idtac "END|prosa.classic.model.priority.Priority.FP_is_total_over_task_set". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.priority.Priority.FP_is_antisymmetric_over_task_set". Abort.
Check @prosa.classic.model.priority.Priority.FP_is_antisymmetric_over_task_set.
Goal True. idtac "END|prosa.classic.model.priority.Priority.FP_is_antisymmetric_over_task_set". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.priority.Priority.JLFP_is_reflexive". Abort.
Check @prosa.classic.model.priority.Priority.JLFP_is_reflexive.
Goal True. idtac "END|prosa.classic.model.priority.Priority.JLFP_is_reflexive". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.priority.Priority.JLFP_is_irreflexive". Abort.
Check @prosa.classic.model.priority.Priority.JLFP_is_irreflexive.
Goal True. idtac "END|prosa.classic.model.priority.Priority.JLFP_is_irreflexive". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.priority.Priority.JLFP_is_transitive". Abort.
Check @prosa.classic.model.priority.Priority.JLFP_is_transitive.
Goal True. idtac "END|prosa.classic.model.priority.Priority.JLFP_is_transitive". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.priority.Priority.JLFP_is_total". Abort.
Check @prosa.classic.model.priority.Priority.JLFP_is_total.
Goal True. idtac "END|prosa.classic.model.priority.Priority.JLFP_is_total". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.priority.Priority.JLFP_respects_sequential_jobs". Abort.
Check @prosa.classic.model.priority.Priority.JLFP_respects_sequential_jobs.
Goal True. idtac "END|prosa.classic.model.priority.Priority.JLFP_respects_sequential_jobs". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.priority.Priority.JLDP_is_reflexive". Abort.
Check @prosa.classic.model.priority.Priority.JLDP_is_reflexive.
Goal True. idtac "END|prosa.classic.model.priority.Priority.JLDP_is_reflexive". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.priority.Priority.JLDP_is_irreflexive". Abort.
Check @prosa.classic.model.priority.Priority.JLDP_is_irreflexive.
Goal True. idtac "END|prosa.classic.model.priority.Priority.JLDP_is_irreflexive". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.priority.Priority.JLDP_is_transitive". Abort.
Check @prosa.classic.model.priority.Priority.JLDP_is_transitive.
Goal True. idtac "END|prosa.classic.model.priority.Priority.JLDP_is_transitive". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.priority.Priority.JLDP_is_total". Abort.
Check @prosa.classic.model.priority.Priority.JLDP_is_total.
Goal True. idtac "END|prosa.classic.model.priority.Priority.JLDP_is_total". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.priority.Priority.RM". Abort.
Check @prosa.classic.model.priority.Priority.RM.
Goal True. idtac "END|prosa.classic.model.priority.Priority.RM". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.priority.Priority.DM". Abort.
Check @prosa.classic.model.priority.Priority.DM.
Goal True. idtac "END|prosa.classic.model.priority.Priority.DM". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.priority.Priority.RM_is_reflexive". Abort.
Check @prosa.classic.model.priority.Priority.RM_is_reflexive.
Goal True. idtac "END|prosa.classic.model.priority.Priority.RM_is_reflexive". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.priority.Priority.RM_is_transitive". Abort.
Check @prosa.classic.model.priority.Priority.RM_is_transitive.
Goal True. idtac "END|prosa.classic.model.priority.Priority.RM_is_transitive". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.priority.Priority.DM_is_reflexive". Abort.
Check @prosa.classic.model.priority.Priority.DM_is_reflexive.
Goal True. idtac "END|prosa.classic.model.priority.Priority.DM_is_reflexive". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.priority.Priority.DM_is_transitive". Abort.
Check @prosa.classic.model.priority.Priority.DM_is_transitive.
Goal True. idtac "END|prosa.classic.model.priority.Priority.DM_is_transitive". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.priority.Priority.any_reflexive_FP_respects_sequential_jobs". Abort.
Check @prosa.classic.model.priority.Priority.any_reflexive_FP_respects_sequential_jobs.
Goal True. idtac "END|prosa.classic.model.priority.Priority.any_reflexive_FP_respects_sequential_jobs". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.priority.Priority.EDF". Abort.
Check @prosa.classic.model.priority.Priority.EDF.
Goal True. idtac "END|prosa.classic.model.priority.Priority.EDF". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.priority.Priority.EDF_is_reflexive". Abort.
Check @prosa.classic.model.priority.Priority.EDF_is_reflexive.
Goal True. idtac "END|prosa.classic.model.priority.Priority.EDF_is_reflexive". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.priority.Priority.EDF_is_transitive". Abort.
Check @prosa.classic.model.priority.Priority.EDF_is_transitive.
Goal True. idtac "END|prosa.classic.model.priority.Priority.EDF_is_transitive". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.priority.Priority.EDF_is_total". Abort.
Check @prosa.classic.model.priority.Priority.EDF_is_total.
Goal True. idtac "END|prosa.classic.model.priority.Priority.EDF_is_total". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.priority.Priority.job_relative_dealine". Abort.
Check @prosa.classic.model.priority.Priority.job_relative_dealine.
Goal True. idtac "END|prosa.classic.model.priority.Priority.job_relative_dealine". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.priority.Priority.EDF_respects_sequential_jobs". Abort.
Check @prosa.classic.model.priority.Priority.EDF_respects_sequential_jobs.
Goal True. idtac "END|prosa.classic.model.priority.Priority.EDF_respects_sequential_jobs". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.priority.Priority.higher_priority_task". Abort.
Check @prosa.classic.model.priority.Priority.higher_priority_task.
Goal True. idtac "END|prosa.classic.model.priority.Priority.higher_priority_task". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.priority.Priority.different_task". Abort.
Check @prosa.classic.model.priority.Priority.different_task.
Goal True. idtac "END|prosa.classic.model.priority.Priority.different_task". Abort.
