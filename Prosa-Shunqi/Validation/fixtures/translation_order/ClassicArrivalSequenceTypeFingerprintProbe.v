(* Recomputes the authoritative `Check @name` fingerprints for classic/model/arrival/basic/arrival_sequence.v. *)
Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.classic.model.arrival.basic.arrival_sequence.
Require Import prosa.classic.model.arrival.basic.task.
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
Goal True. idtac "BEGIN|prosa.classic.model.arrival.basic.arrival_sequence.ArrivalSequence.arrival_sequence". Abort.
Check @prosa.classic.model.arrival.basic.arrival_sequence.ArrivalSequence.arrival_sequence.
Goal True. idtac "END|prosa.classic.model.arrival.basic.arrival_sequence.ArrivalSequence.arrival_sequence". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.arrival.basic.arrival_sequence.ArrivalSequence.jobs_arriving_at". Abort.
Check @prosa.classic.model.arrival.basic.arrival_sequence.ArrivalSequence.jobs_arriving_at.
Goal True. idtac "END|prosa.classic.model.arrival.basic.arrival_sequence.ArrivalSequence.jobs_arriving_at". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.arrival.basic.arrival_sequence.ArrivalSequence.arrives_at". Abort.
Check @prosa.classic.model.arrival.basic.arrival_sequence.ArrivalSequence.arrives_at.
Goal True. idtac "END|prosa.classic.model.arrival.basic.arrival_sequence.ArrivalSequence.arrives_at". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.arrival.basic.arrival_sequence.ArrivalSequence.arrives_in". Abort.
Check @prosa.classic.model.arrival.basic.arrival_sequence.ArrivalSequence.arrives_in.
Goal True. idtac "END|prosa.classic.model.arrival.basic.arrival_sequence.ArrivalSequence.arrives_in". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.arrival.basic.arrival_sequence.ArrivalSequence.arrival_times_are_consistent". Abort.
Check @prosa.classic.model.arrival.basic.arrival_sequence.ArrivalSequence.arrival_times_are_consistent.
Goal True. idtac "END|prosa.classic.model.arrival.basic.arrival_sequence.ArrivalSequence.arrival_times_are_consistent". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.arrival.basic.arrival_sequence.ArrivalSequence.arrival_sequence_is_a_set". Abort.
Check @prosa.classic.model.arrival.basic.arrival_sequence.ArrivalSequence.arrival_sequence_is_a_set.
Goal True. idtac "END|prosa.classic.model.arrival.basic.arrival_sequence.ArrivalSequence.arrival_sequence_is_a_set". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.arrival.basic.arrival_sequence.ArrivalSequence.has_arrived". Abort.
Check @prosa.classic.model.arrival.basic.arrival_sequence.ArrivalSequence.has_arrived.
Goal True. idtac "END|prosa.classic.model.arrival.basic.arrival_sequence.ArrivalSequence.has_arrived". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.arrival.basic.arrival_sequence.ArrivalSequence.arrived_before". Abort.
Check @prosa.classic.model.arrival.basic.arrival_sequence.ArrivalSequence.arrived_before.
Goal True. idtac "END|prosa.classic.model.arrival.basic.arrival_sequence.ArrivalSequence.arrived_before". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.arrival.basic.arrival_sequence.ArrivalSequence.arrived_between". Abort.
Check @prosa.classic.model.arrival.basic.arrival_sequence.ArrivalSequence.arrived_between.
Goal True. idtac "END|prosa.classic.model.arrival.basic.arrival_sequence.ArrivalSequence.arrived_between". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.arrival.basic.arrival_sequence.ArrivalSequence.jobs_arrived_between". Abort.
Check @prosa.classic.model.arrival.basic.arrival_sequence.ArrivalSequence.jobs_arrived_between.
Goal True. idtac "END|prosa.classic.model.arrival.basic.arrival_sequence.ArrivalSequence.jobs_arrived_between". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.arrival.basic.arrival_sequence.ArrivalSequence.jobs_arrived_up_to". Abort.
Check @prosa.classic.model.arrival.basic.arrival_sequence.ArrivalSequence.jobs_arrived_up_to.
Goal True. idtac "END|prosa.classic.model.arrival.basic.arrival_sequence.ArrivalSequence.jobs_arrived_up_to". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.arrival.basic.arrival_sequence.ArrivalSequence.jobs_arrived_before". Abort.
Check @prosa.classic.model.arrival.basic.arrival_sequence.ArrivalSequence.jobs_arrived_before.
Goal True. idtac "END|prosa.classic.model.arrival.basic.arrival_sequence.ArrivalSequence.jobs_arrived_before". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.arrival.basic.arrival_sequence.ArrivalSequence.job_arrived_between_cat". Abort.
Check @prosa.classic.model.arrival.basic.arrival_sequence.ArrivalSequence.job_arrived_between_cat.
Goal True. idtac "END|prosa.classic.model.arrival.basic.arrival_sequence.ArrivalSequence.job_arrived_between_cat". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.arrival.basic.arrival_sequence.ArrivalSequence.jobs_arrived_between_mem_cat". Abort.
Check @prosa.classic.model.arrival.basic.arrival_sequence.ArrivalSequence.jobs_arrived_between_mem_cat.
Goal True. idtac "END|prosa.classic.model.arrival.basic.arrival_sequence.ArrivalSequence.jobs_arrived_between_mem_cat". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.arrival.basic.arrival_sequence.ArrivalSequence.jobs_arrived_between_sub". Abort.
Check @prosa.classic.model.arrival.basic.arrival_sequence.ArrivalSequence.jobs_arrived_between_sub.
Goal True. idtac "END|prosa.classic.model.arrival.basic.arrival_sequence.ArrivalSequence.jobs_arrived_between_sub". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.arrival.basic.arrival_sequence.ArrivalSequence.in_arrivals_implies_arrived". Abort.
Check @prosa.classic.model.arrival.basic.arrival_sequence.ArrivalSequence.in_arrivals_implies_arrived.
Goal True. idtac "END|prosa.classic.model.arrival.basic.arrival_sequence.ArrivalSequence.in_arrivals_implies_arrived". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.arrival.basic.arrival_sequence.ArrivalSequence.in_arrivals_implies_arrived_between". Abort.
Check @prosa.classic.model.arrival.basic.arrival_sequence.ArrivalSequence.in_arrivals_implies_arrived_between.
Goal True. idtac "END|prosa.classic.model.arrival.basic.arrival_sequence.ArrivalSequence.in_arrivals_implies_arrived_between". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.arrival.basic.arrival_sequence.ArrivalSequence.in_arrivals_implies_arrived_before". Abort.
Check @prosa.classic.model.arrival.basic.arrival_sequence.ArrivalSequence.in_arrivals_implies_arrived_before.
Goal True. idtac "END|prosa.classic.model.arrival.basic.arrival_sequence.ArrivalSequence.in_arrivals_implies_arrived_before". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.arrival.basic.arrival_sequence.ArrivalSequence.arrived_between_implies_in_arrivals". Abort.
Check @prosa.classic.model.arrival.basic.arrival_sequence.ArrivalSequence.arrived_between_implies_in_arrivals.
Goal True. idtac "END|prosa.classic.model.arrival.basic.arrival_sequence.ArrivalSequence.arrived_between_implies_in_arrivals". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.arrival.basic.arrival_sequence.ArrivalSequence.arrivals_uniq". Abort.
Check @prosa.classic.model.arrival.basic.arrival_sequence.ArrivalSequence.arrivals_uniq.
Goal True. idtac "END|prosa.classic.model.arrival.basic.arrival_sequence.ArrivalSequence.arrivals_uniq". Abort.
