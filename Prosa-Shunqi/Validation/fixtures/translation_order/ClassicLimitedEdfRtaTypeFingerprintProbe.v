(* Recomputes the authoritative `Check @name` fingerprints for classic/model/schedule/uni/limited/edf/response_time_bound.v. *)
Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.classic.analysis.uni.arrival_curves.workload_bound.
Require Import prosa.classic.model.arrival.basic.arrival_sequence.
Require Import prosa.classic.model.arrival.basic.job.
Require Import prosa.classic.model.arrival.basic.task.
Require Import prosa.classic.model.arrival.basic.task_arrival.
Require Import prosa.classic.model.arrival.curves.bounds.
Require Import prosa.classic.model.priority.
Require Import prosa.classic.model.schedule.uni.basic.platform.
Require Import prosa.classic.model.schedule.uni.limited.abstract_RTA.abstract_rta.
Require Import prosa.classic.model.schedule.uni.limited.abstract_RTA.abstract_seq_rta.
Require Import prosa.classic.model.schedule.uni.limited.abstract_RTA.definitions.
Require Import prosa.classic.model.schedule.uni.limited.abstract_RTA.reduction_of_search_space.
Require Import prosa.classic.model.schedule.uni.limited.abstract_RTA.sufficient_condition_for_lock_in_service.
Require Import prosa.classic.model.schedule.uni.limited.busy_interval.
Require Import prosa.classic.model.schedule.uni.limited.edf.response_time_bound.
Require Import prosa.classic.model.schedule.uni.limited.jlfp_instantiation.
Require Import prosa.classic.model.schedule.uni.limited.platform.definitions.
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
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.edf.response_time_bound.AbstractRTAforEDFwithArrivalCurves.task_rbf_changes_at". Abort.
Check @prosa.classic.model.schedule.uni.limited.edf.response_time_bound.AbstractRTAforEDFwithArrivalCurves.task_rbf_changes_at.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.edf.response_time_bound.AbstractRTAforEDFwithArrivalCurves.task_rbf_changes_at". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.edf.response_time_bound.AbstractRTAforEDFwithArrivalCurves.bound_on_total_hep_workload_changes_at". Abort.
Check @prosa.classic.model.schedule.uni.limited.edf.response_time_bound.AbstractRTAforEDFwithArrivalCurves.bound_on_total_hep_workload_changes_at.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.edf.response_time_bound.AbstractRTAforEDFwithArrivalCurves.bound_on_total_hep_workload_changes_at". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.edf.response_time_bound.AbstractRTAforEDFwithArrivalCurves.instantiated_i_and_w_are_coherent_with_schedule". Abort.
Check @prosa.classic.model.schedule.uni.limited.edf.response_time_bound.AbstractRTAforEDFwithArrivalCurves.instantiated_i_and_w_are_coherent_with_schedule.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.edf.response_time_bound.AbstractRTAforEDFwithArrivalCurves.instantiated_i_and_w_are_coherent_with_schedule". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.edf.response_time_bound.AbstractRTAforEDFwithArrivalCurves.instantiated_interference_and_workload_consistent_with_sequential_jobs". Abort.
Check @prosa.classic.model.schedule.uni.limited.edf.response_time_bound.AbstractRTAforEDFwithArrivalCurves.instantiated_interference_and_workload_consistent_with_sequential_jobs.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.edf.response_time_bound.AbstractRTAforEDFwithArrivalCurves.instantiated_interference_and_workload_consistent_with_sequential_jobs". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.edf.response_time_bound.AbstractRTAforEDFwithArrivalCurves.instantiated_busy_intervals_are_bounded". Abort.
Check @prosa.classic.model.schedule.uni.limited.edf.response_time_bound.AbstractRTAforEDFwithArrivalCurves.instantiated_busy_intervals_are_bounded.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.edf.response_time_bound.AbstractRTAforEDFwithArrivalCurves.instantiated_busy_intervals_are_bounded". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.edf.response_time_bound.AbstractRTAforEDFwithArrivalCurves.instantiated_task_interference_is_bounded". Abort.
Check @prosa.classic.model.schedule.uni.limited.edf.response_time_bound.AbstractRTAforEDFwithArrivalCurves.instantiated_task_interference_is_bounded.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.edf.response_time_bound.AbstractRTAforEDFwithArrivalCurves.instantiated_task_interference_is_bounded". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.edf.response_time_bound.AbstractRTAforEDFwithArrivalCurves.A_is_in_concrete_search_space". Abort.
Check @prosa.classic.model.schedule.uni.limited.edf.response_time_bound.AbstractRTAforEDFwithArrivalCurves.A_is_in_concrete_search_space.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.edf.response_time_bound.AbstractRTAforEDFwithArrivalCurves.A_is_in_concrete_search_space". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.edf.response_time_bound.AbstractRTAforEDFwithArrivalCurves.correct_search_space". Abort.
Check @prosa.classic.model.schedule.uni.limited.edf.response_time_bound.AbstractRTAforEDFwithArrivalCurves.correct_search_space.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.edf.response_time_bound.AbstractRTAforEDFwithArrivalCurves.correct_search_space". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.edf.response_time_bound.AbstractRTAforEDFwithArrivalCurves.uniprocessor_response_time_bound_edf". Abort.
Check @prosa.classic.model.schedule.uni.limited.edf.response_time_bound.AbstractRTAforEDFwithArrivalCurves.uniprocessor_response_time_bound_edf.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.edf.response_time_bound.AbstractRTAforEDFwithArrivalCurves.uniprocessor_response_time_bound_edf". Abort.
