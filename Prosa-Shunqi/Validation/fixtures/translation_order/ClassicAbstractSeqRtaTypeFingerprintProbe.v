(* Recomputes the authoritative `Check @name` fingerprints for classic/model/schedule/uni/limited/abstract_RTA/abstract_seq_rta.v. *)
Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.classic.analysis.uni.arrival_curves.workload_bound.
Require Import prosa.classic.model.arrival.basic.arrival_sequence.
Require Import prosa.classic.model.arrival.basic.job.
Require Import prosa.classic.model.arrival.basic.task.
Require Import prosa.classic.model.arrival.basic.task_arrival.
Require Import prosa.classic.model.arrival.curves.bounds.
Require Import prosa.classic.model.priority.
Require Import prosa.classic.model.schedule.uni.limited.abstract_RTA.abstract_rta.
Require Import prosa.classic.model.schedule.uni.limited.abstract_RTA.abstract_seq_rta.
Require Import prosa.classic.model.schedule.uni.limited.abstract_RTA.definitions.
Require Import prosa.classic.model.schedule.uni.limited.abstract_RTA.reduction_of_search_space.
Require Import prosa.classic.model.schedule.uni.limited.abstract_RTA.sufficient_condition_for_lock_in_service.
Require Import prosa.classic.model.schedule.uni.limited.rbf.
Require Import prosa.classic.model.schedule.uni.limited.schedule.
Require Import prosa.classic.model.schedule.uni.nonpreemptive.schedule.
Require Import prosa.classic.model.schedule.uni.response_time.
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
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.abstract_RTA.abstract_seq_rta.AbstractSeqRTA.interference_and_workload_consistent_with_sequential_jobs". Abort.
Check @prosa.classic.model.schedule.uni.limited.abstract_RTA.abstract_seq_rta.AbstractSeqRTA.interference_and_workload_consistent_with_sequential_jobs.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.abstract_RTA.abstract_seq_rta.AbstractSeqRTA.interference_and_workload_consistent_with_sequential_jobs". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.abstract_RTA.abstract_seq_rta.AbstractSeqRTA.task_interference_received_before". Abort.
Check @prosa.classic.model.schedule.uni.limited.abstract_RTA.abstract_seq_rta.AbstractSeqRTA.task_interference_received_before.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.abstract_RTA.abstract_seq_rta.AbstractSeqRTA.task_interference_received_before". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.abstract_RTA.abstract_seq_rta.AbstractSeqRTA.cumul_task_interference". Abort.
Check @prosa.classic.model.schedule.uni.limited.abstract_RTA.abstract_seq_rta.AbstractSeqRTA.cumul_task_interference.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.abstract_RTA.abstract_seq_rta.AbstractSeqRTA.cumul_task_interference". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.abstract_RTA.abstract_seq_rta.AbstractSeqRTA.task_interference_is_bounded_by". Abort.
Check @prosa.classic.model.schedule.uni.limited.abstract_RTA.abstract_seq_rta.AbstractSeqRTA.task_interference_is_bounded_by.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.abstract_RTA.abstract_seq_rta.AbstractSeqRTA.task_interference_is_bounded_by". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.abstract_RTA.abstract_seq_rta.AbstractSeqRTA.completed_before_beginning_of_busy_interval". Abort.
Check @prosa.classic.model.schedule.uni.limited.abstract_RTA.abstract_seq_rta.AbstractSeqRTA.completed_before_beginning_of_busy_interval.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.abstract_RTA.abstract_seq_rta.AbstractSeqRTA.completed_before_beginning_of_busy_interval". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.abstract_RTA.abstract_seq_rta.AbstractSeqRTA.arrives_after_beginning_of_busy_interval". Abort.
Check @prosa.classic.model.schedule.uni.limited.abstract_RTA.abstract_seq_rta.AbstractSeqRTA.arrives_after_beginning_of_busy_interval.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.abstract_RTA.abstract_seq_rta.AbstractSeqRTA.arrives_after_beginning_of_busy_interval". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.abstract_RTA.abstract_seq_rta.AbstractSeqRTA.bound_for_cumulative_job_interference_actual". Abort.
Check @prosa.classic.model.schedule.uni.limited.abstract_RTA.abstract_seq_rta.AbstractSeqRTA.bound_for_cumulative_job_interference_actual.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.abstract_RTA.abstract_seq_rta.AbstractSeqRTA.bound_for_cumulative_job_interference_actual". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.abstract_RTA.abstract_seq_rta.AbstractSeqRTA.task_rbf_excl_tsk_bounds_task_workload_excl_j". Abort.
Check @prosa.classic.model.schedule.uni.limited.abstract_RTA.abstract_seq_rta.AbstractSeqRTA.task_rbf_excl_tsk_bounds_task_workload_excl_j.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.abstract_RTA.abstract_seq_rta.AbstractSeqRTA.task_rbf_excl_tsk_bounds_task_workload_excl_j". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.abstract_RTA.abstract_seq_rta.AbstractSeqRTA.bound_for_cumulative_job_interference". Abort.
Check @prosa.classic.model.schedule.uni.limited.abstract_RTA.abstract_seq_rta.AbstractSeqRTA.bound_for_cumulative_job_interference.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.abstract_RTA.abstract_seq_rta.AbstractSeqRTA.bound_for_cumulative_job_interference". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.abstract_RTA.abstract_seq_rta.AbstractSeqRTA.max_in_seq_hypothesis_implies_max_in_nonseq_hypothesis". Abort.
Check @prosa.classic.model.schedule.uni.limited.abstract_RTA.abstract_seq_rta.AbstractSeqRTA.max_in_seq_hypothesis_implies_max_in_nonseq_hypothesis.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.abstract_RTA.abstract_seq_rta.AbstractSeqRTA.max_in_seq_hypothesis_implies_max_in_nonseq_hypothesis". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.abstract_RTA.abstract_seq_rta.AbstractSeqRTA.uniprocessor_response_time_bound_seq". Abort.
Check @prosa.classic.model.schedule.uni.limited.abstract_RTA.abstract_seq_rta.AbstractSeqRTA.uniprocessor_response_time_bound_seq.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.abstract_RTA.abstract_seq_rta.AbstractSeqRTA.uniprocessor_response_time_bound_seq". Abort.
