(* Recomputes the authoritative `Check @name` fingerprints for classic/model/schedule/uni/limited/jlfp_instantiation.v. *)
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
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.jlfp_instantiation.JLFPInstantiation.is_interference_from_another_job_with_higher_eq_priority". Abort.
Check @prosa.classic.model.schedule.uni.limited.jlfp_instantiation.JLFPInstantiation.is_interference_from_another_job_with_higher_eq_priority.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.jlfp_instantiation.JLFPInstantiation.is_interference_from_another_job_with_higher_eq_priority". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.jlfp_instantiation.JLFPInstantiation.is_interference_from_another_task_with_higher_eq_priority". Abort.
Check @prosa.classic.model.schedule.uni.limited.jlfp_instantiation.JLFPInstantiation.is_interference_from_another_task_with_higher_eq_priority.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.jlfp_instantiation.JLFPInstantiation.is_interference_from_another_task_with_higher_eq_priority". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.jlfp_instantiation.JLFPInstantiation.interfering_workload_of_jobs_with_hep_priority". Abort.
Check @prosa.classic.model.schedule.uni.limited.jlfp_instantiation.JLFPInstantiation.interfering_workload_of_jobs_with_hep_priority.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.jlfp_instantiation.JLFPInstantiation.interfering_workload_of_jobs_with_hep_priority". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.jlfp_instantiation.JLFPInstantiation.interference". Abort.
Check @prosa.classic.model.schedule.uni.limited.jlfp_instantiation.JLFPInstantiation.interference.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.jlfp_instantiation.JLFPInstantiation.interference". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.jlfp_instantiation.JLFPInstantiation.interfering_workload". Abort.
Check @prosa.classic.model.schedule.uni.limited.jlfp_instantiation.JLFPInstantiation.interfering_workload.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.jlfp_instantiation.JLFPInstantiation.interfering_workload". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.jlfp_instantiation.JLFPInstantiation.cumulative_interference_split". Abort.
Check @prosa.classic.model.schedule.uni.limited.jlfp_instantiation.JLFPInstantiation.cumulative_interference_split.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.jlfp_instantiation.JLFPInstantiation.cumulative_interference_split". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.jlfp_instantiation.JLFPInstantiation.cumulative_task_interference_split". Abort.
Check @prosa.classic.model.schedule.uni.limited.jlfp_instantiation.JLFPInstantiation.cumulative_task_interference_split.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.jlfp_instantiation.JLFPInstantiation.cumulative_task_interference_split". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.jlfp_instantiation.JLFPInstantiation.instantiated_cumulative_workload_of_hep_jobs_equal_total_workload_of_hep_jobs". Abort.
Check @prosa.classic.model.schedule.uni.limited.jlfp_instantiation.JLFPInstantiation.instantiated_cumulative_workload_of_hep_jobs_equal_total_workload_of_hep_jobs.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.jlfp_instantiation.JLFPInstantiation.instantiated_cumulative_workload_of_hep_jobs_equal_total_workload_of_hep_jobs". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.jlfp_instantiation.JLFPInstantiation.instantiated_cumulative_interference_of_hep_jobs_equal_total_interference_of_hep_jobs". Abort.
Check @prosa.classic.model.schedule.uni.limited.jlfp_instantiation.JLFPInstantiation.instantiated_cumulative_interference_of_hep_jobs_equal_total_interference_of_hep_jobs.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.jlfp_instantiation.JLFPInstantiation.instantiated_cumulative_interference_of_hep_jobs_equal_total_interference_of_hep_jobs". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.jlfp_instantiation.JLFPInstantiation.instantiated_cumulative_interference_of_hep_tasks_equal_total_interference_of_hep_tasks". Abort.
Check @prosa.classic.model.schedule.uni.limited.jlfp_instantiation.JLFPInstantiation.instantiated_cumulative_interference_of_hep_tasks_equal_total_interference_of_hep_tasks.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.jlfp_instantiation.JLFPInstantiation.instantiated_cumulative_interference_of_hep_tasks_equal_total_interference_of_hep_tasks". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.jlfp_instantiation.JLFPInstantiation.instantiated_quiet_time_equivalent_edf_quiet_time". Abort.
Check @prosa.classic.model.schedule.uni.limited.jlfp_instantiation.JLFPInstantiation.instantiated_quiet_time_equivalent_edf_quiet_time.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.jlfp_instantiation.JLFPInstantiation.instantiated_quiet_time_equivalent_edf_quiet_time". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.limited.jlfp_instantiation.JLFPInstantiation.instantiated_busy_interval_equivalent_edf_busy_interval". Abort.
Check @prosa.classic.model.schedule.uni.limited.jlfp_instantiation.JLFPInstantiation.instantiated_busy_interval_equivalent_edf_busy_interval.
Goal True. idtac "END|prosa.classic.model.schedule.uni.limited.jlfp_instantiation.JLFPInstantiation.instantiated_busy_interval_equivalent_edf_busy_interval". Abort.
