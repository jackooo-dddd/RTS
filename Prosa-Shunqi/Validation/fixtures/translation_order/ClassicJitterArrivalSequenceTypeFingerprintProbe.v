(* Recomputes the authoritative `Check @name` fingerprints for classic/model/arrival/jitter/arrival_sequence.v. *)
Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.classic.model.arrival.basic.arrival_sequence.
Require Import prosa.classic.model.arrival.basic.task.
Require Import prosa.classic.model.arrival.jitter.arrival_sequence.
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
Goal True. idtac "BEGIN|prosa.classic.model.arrival.jitter.arrival_sequence.ArrivalSequenceWithJitter.actual_arrival". Abort.
Check @prosa.classic.model.arrival.jitter.arrival_sequence.ArrivalSequenceWithJitter.actual_arrival.
Goal True. idtac "END|prosa.classic.model.arrival.jitter.arrival_sequence.ArrivalSequenceWithJitter.actual_arrival". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.arrival.jitter.arrival_sequence.ArrivalSequenceWithJitter.jitter_has_passed". Abort.
Check @prosa.classic.model.arrival.jitter.arrival_sequence.ArrivalSequenceWithJitter.jitter_has_passed.
Goal True. idtac "END|prosa.classic.model.arrival.jitter.arrival_sequence.ArrivalSequenceWithJitter.jitter_has_passed". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.arrival.jitter.arrival_sequence.ArrivalSequenceWithJitter.actual_arrival_before". Abort.
Check @prosa.classic.model.arrival.jitter.arrival_sequence.ArrivalSequenceWithJitter.actual_arrival_before.
Goal True. idtac "END|prosa.classic.model.arrival.jitter.arrival_sequence.ArrivalSequenceWithJitter.actual_arrival_before". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.arrival.jitter.arrival_sequence.ArrivalSequenceWithJitter.actual_arrival_between". Abort.
Check @prosa.classic.model.arrival.jitter.arrival_sequence.ArrivalSequenceWithJitter.actual_arrival_between.
Goal True. idtac "END|prosa.classic.model.arrival.jitter.arrival_sequence.ArrivalSequenceWithJitter.actual_arrival_between". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.arrival.jitter.arrival_sequence.ArrivalSequenceWithJitter.actual_arrivals_between". Abort.
Check @prosa.classic.model.arrival.jitter.arrival_sequence.ArrivalSequenceWithJitter.actual_arrivals_between.
Goal True. idtac "END|prosa.classic.model.arrival.jitter.arrival_sequence.ArrivalSequenceWithJitter.actual_arrivals_between". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.arrival.jitter.arrival_sequence.ArrivalSequenceWithJitter.actual_arrivals_up_to". Abort.
Check @prosa.classic.model.arrival.jitter.arrival_sequence.ArrivalSequenceWithJitter.actual_arrivals_up_to.
Goal True. idtac "END|prosa.classic.model.arrival.jitter.arrival_sequence.ArrivalSequenceWithJitter.actual_arrivals_up_to". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.arrival.jitter.arrival_sequence.ArrivalSequenceWithJitter.actual_arrivals_before". Abort.
Check @prosa.classic.model.arrival.jitter.arrival_sequence.ArrivalSequenceWithJitter.actual_arrivals_before.
Goal True. idtac "END|prosa.classic.model.arrival.jitter.arrival_sequence.ArrivalSequenceWithJitter.actual_arrivals_before". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.arrival.jitter.arrival_sequence.ArrivalSequenceWithJitter.actual_arrivals_between_mem_cat". Abort.
Check @prosa.classic.model.arrival.jitter.arrival_sequence.ArrivalSequenceWithJitter.actual_arrivals_between_mem_cat.
Goal True. idtac "END|prosa.classic.model.arrival.jitter.arrival_sequence.ArrivalSequenceWithJitter.actual_arrivals_between_mem_cat". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.arrival.jitter.arrival_sequence.ArrivalSequenceWithJitter.actual_arrivals_between_sub". Abort.
Check @prosa.classic.model.arrival.jitter.arrival_sequence.ArrivalSequenceWithJitter.actual_arrivals_between_sub.
Goal True. idtac "END|prosa.classic.model.arrival.jitter.arrival_sequence.ArrivalSequenceWithJitter.actual_arrivals_between_sub". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.arrival.jitter.arrival_sequence.ArrivalSequenceWithJitter.in_actual_arrivals_between_implies_arrived". Abort.
Check @prosa.classic.model.arrival.jitter.arrival_sequence.ArrivalSequenceWithJitter.in_actual_arrivals_between_implies_arrived.
Goal True. idtac "END|prosa.classic.model.arrival.jitter.arrival_sequence.ArrivalSequenceWithJitter.in_actual_arrivals_between_implies_arrived". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.arrival.jitter.arrival_sequence.ArrivalSequenceWithJitter.in_actual_arrivals_before_implies_arrived". Abort.
Check @prosa.classic.model.arrival.jitter.arrival_sequence.ArrivalSequenceWithJitter.in_actual_arrivals_before_implies_arrived.
Goal True. idtac "END|prosa.classic.model.arrival.jitter.arrival_sequence.ArrivalSequenceWithJitter.in_actual_arrivals_before_implies_arrived". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.arrival.jitter.arrival_sequence.ArrivalSequenceWithJitter.in_actual_arrivals_implies_arrived_before". Abort.
Check @prosa.classic.model.arrival.jitter.arrival_sequence.ArrivalSequenceWithJitter.in_actual_arrivals_implies_arrived_before.
Goal True. idtac "END|prosa.classic.model.arrival.jitter.arrival_sequence.ArrivalSequenceWithJitter.in_actual_arrivals_implies_arrived_before". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.arrival.jitter.arrival_sequence.ArrivalSequenceWithJitter.in_actual_arrivals_implies_arrived_between". Abort.
Check @prosa.classic.model.arrival.jitter.arrival_sequence.ArrivalSequenceWithJitter.in_actual_arrivals_implies_arrived_between.
Goal True. idtac "END|prosa.classic.model.arrival.jitter.arrival_sequence.ArrivalSequenceWithJitter.in_actual_arrivals_implies_arrived_between". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.arrival.jitter.arrival_sequence.ArrivalSequenceWithJitter.arrived_between_implies_in_actual_arrivals". Abort.
Check @prosa.classic.model.arrival.jitter.arrival_sequence.ArrivalSequenceWithJitter.arrived_between_implies_in_actual_arrivals.
Goal True. idtac "END|prosa.classic.model.arrival.jitter.arrival_sequence.ArrivalSequenceWithJitter.arrived_between_implies_in_actual_arrivals". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.arrival.jitter.arrival_sequence.ArrivalSequenceWithJitter.actual_arrivals_uniq". Abort.
Check @prosa.classic.model.arrival.jitter.arrival_sequence.ArrivalSequenceWithJitter.actual_arrivals_uniq.
Goal True. idtac "END|prosa.classic.model.arrival.jitter.arrival_sequence.ArrivalSequenceWithJitter.actual_arrivals_uniq". Abort.
