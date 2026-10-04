(* Recomputes the authoritative `Check @name` fingerprints for classic/model/policy_tdma.v. *)
Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.classic.model.arrival.basic.arrival_sequence.
Require Import prosa.classic.model.arrival.basic.job.
Require Import prosa.classic.model.arrival.basic.task.
Require Import prosa.classic.model.policy_tdma.
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
Goal True. idtac "BEGIN|prosa.classic.model.policy_tdma.PolicyTDMA.TDMA_slot". Abort.
Check @prosa.classic.model.policy_tdma.PolicyTDMA.TDMA_slot.
Goal True. idtac "END|prosa.classic.model.policy_tdma.PolicyTDMA.TDMA_slot". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.policy_tdma.PolicyTDMA.TDMA_slot_order". Abort.
Check @prosa.classic.model.policy_tdma.PolicyTDMA.TDMA_slot_order.
Goal True. idtac "END|prosa.classic.model.policy_tdma.PolicyTDMA.TDMA_slot_order". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.policy_tdma.PolicyTDMA.slot_order_is_transitive". Abort.
Check @prosa.classic.model.policy_tdma.PolicyTDMA.slot_order_is_transitive.
Goal True. idtac "END|prosa.classic.model.policy_tdma.PolicyTDMA.slot_order_is_transitive". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.policy_tdma.PolicyTDMA.slot_order_is_total_over_task_set". Abort.
Check @prosa.classic.model.policy_tdma.PolicyTDMA.slot_order_is_total_over_task_set.
Goal True. idtac "END|prosa.classic.model.policy_tdma.PolicyTDMA.slot_order_is_total_over_task_set". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.policy_tdma.PolicyTDMA.slot_order_is_antisymmetric_over_task_set". Abort.
Check @prosa.classic.model.policy_tdma.PolicyTDMA.slot_order_is_antisymmetric_over_task_set.
Goal True. idtac "END|prosa.classic.model.policy_tdma.PolicyTDMA.slot_order_is_antisymmetric_over_task_set". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.policy_tdma.PolicyTDMA.is_valid_time_slot". Abort.
Check @prosa.classic.model.policy_tdma.PolicyTDMA.is_valid_time_slot.
Goal True. idtac "END|prosa.classic.model.policy_tdma.PolicyTDMA.is_valid_time_slot". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.policy_tdma.PolicyTDMA.TDMA_cycle". Abort.
Check @prosa.classic.model.policy_tdma.PolicyTDMA.TDMA_cycle.
Goal True. idtac "END|prosa.classic.model.policy_tdma.PolicyTDMA.TDMA_cycle". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.policy_tdma.PolicyTDMA.Task_slot_offset". Abort.
Check @prosa.classic.model.policy_tdma.PolicyTDMA.Task_slot_offset.
Goal True. idtac "END|prosa.classic.model.policy_tdma.PolicyTDMA.Task_slot_offset". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.policy_tdma.PolicyTDMA.Task_in_time_slot". Abort.
Check @prosa.classic.model.policy_tdma.PolicyTDMA.Task_in_time_slot.
Goal True. idtac "END|prosa.classic.model.policy_tdma.PolicyTDMA.Task_in_time_slot". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.policy_tdma.PolicyTDMA.TDMA_cycle_ge_each_time_slot". Abort.
Check @prosa.classic.model.policy_tdma.PolicyTDMA.TDMA_cycle_ge_each_time_slot.
Goal True. idtac "END|prosa.classic.model.policy_tdma.PolicyTDMA.TDMA_cycle_ge_each_time_slot". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.policy_tdma.PolicyTDMA.TDMA_cycle_positive". Abort.
Check @prosa.classic.model.policy_tdma.PolicyTDMA.TDMA_cycle_positive.
Goal True. idtac "END|prosa.classic.model.policy_tdma.PolicyTDMA.TDMA_cycle_positive". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.policy_tdma.PolicyTDMA.Offset_lt_cycle". Abort.
Check @prosa.classic.model.policy_tdma.PolicyTDMA.Offset_lt_cycle.
Goal True. idtac "END|prosa.classic.model.policy_tdma.PolicyTDMA.Offset_lt_cycle". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.policy_tdma.PolicyTDMA.Offset_add_slot_leq_cycle". Abort.
Check @prosa.classic.model.policy_tdma.PolicyTDMA.Offset_add_slot_leq_cycle.
Goal True. idtac "END|prosa.classic.model.policy_tdma.PolicyTDMA.Offset_add_slot_leq_cycle". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.policy_tdma.PolicyTDMA.relation_offset". Abort.
Check @prosa.classic.model.policy_tdma.PolicyTDMA.relation_offset.
Goal True. idtac "END|prosa.classic.model.policy_tdma.PolicyTDMA.relation_offset". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.policy_tdma.PolicyTDMA.task_in_time_slot_uniq". Abort.
Check @prosa.classic.model.policy_tdma.PolicyTDMA.task_in_time_slot_uniq.
Goal True. idtac "END|prosa.classic.model.policy_tdma.PolicyTDMA.task_in_time_slot_uniq". Abort.
