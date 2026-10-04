(* Recomputes the authoritative `Check @name` fingerprints for classic/model/schedule/uni/service.v. *)
Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.classic.model.arrival.basic.arrival_sequence.
Require Import prosa.classic.model.arrival.basic.job.
Require Import prosa.classic.model.arrival.basic.task.
Require Import prosa.classic.model.priority.
Require Import prosa.classic.model.schedule.uni.schedule.
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
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.service.Service.service_of_jobs". Abort.
Check @prosa.classic.model.schedule.uni.service.Service.service_of_jobs.
Goal True. idtac "END|prosa.classic.model.schedule.uni.service.Service.service_of_jobs". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.service.Service.service_of_higher_or_equal_priority_tasks". Abort.
Check @prosa.classic.model.schedule.uni.service.Service.service_of_higher_or_equal_priority_tasks.
Goal True. idtac "END|prosa.classic.model.schedule.uni.service.Service.service_of_higher_or_equal_priority_tasks". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.service.Service.service_of_higher_or_equal_priority_jobs". Abort.
Check @prosa.classic.model.schedule.uni.service.Service.service_of_higher_or_equal_priority_jobs.
Goal True. idtac "END|prosa.classic.model.schedule.uni.service.Service.service_of_higher_or_equal_priority_jobs". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.service.Service.service_of_jobs_le_workload". Abort.
Check @prosa.classic.model.schedule.uni.service.Service.service_of_jobs_le_workload.
Goal True. idtac "END|prosa.classic.model.schedule.uni.service.Service.service_of_jobs_le_workload". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.service.Service.service_of_jobs_le_delta". Abort.
Check @prosa.classic.model.schedule.uni.service.Service.service_of_jobs_le_delta.
Goal True. idtac "END|prosa.classic.model.schedule.uni.service.Service.service_of_jobs_le_delta". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.service.Service.task_service_of_jobs_received_in". Abort.
Check @prosa.classic.model.schedule.uni.service.Service.task_service_of_jobs_received_in.
Goal True. idtac "END|prosa.classic.model.schedule.uni.service.Service.task_service_of_jobs_received_in". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.service.Service.task_service_between". Abort.
Check @prosa.classic.model.schedule.uni.service.Service.task_service_between.
Goal True. idtac "END|prosa.classic.model.schedule.uni.service.Service.task_service_between". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.service.Service.service_monotonic". Abort.
Check @prosa.classic.model.schedule.uni.service.Service.service_monotonic.
Goal True. idtac "END|prosa.classic.model.schedule.uni.service.Service.service_monotonic". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.service.Service.service_during_cat". Abort.
Check @prosa.classic.model.schedule.uni.service.Service.service_during_cat.
Goal True. idtac "END|prosa.classic.model.schedule.uni.service.Service.service_during_cat". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.service.Service.incremental_service_during". Abort.
Check @prosa.classic.model.schedule.uni.service.Service.incremental_service_during.
Goal True. idtac "END|prosa.classic.model.schedule.uni.service.Service.incremental_service_during". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.service.Service.service_of_jobs_le_1". Abort.
Check @prosa.classic.model.schedule.uni.service.Service.service_of_jobs_le_1.
Goal True. idtac "END|prosa.classic.model.schedule.uni.service.Service.service_of_jobs_le_1". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.service.Service.total_service_of_jobs_le_delta". Abort.
Check @prosa.classic.model.schedule.uni.service.Service.total_service_of_jobs_le_delta.
Goal True. idtac "END|prosa.classic.model.schedule.uni.service.Service.total_service_of_jobs_le_delta". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.service.Service.low_service_implies_existence_of_idle_time". Abort.
Check @prosa.classic.model.schedule.uni.service.Service.low_service_implies_existence_of_idle_time.
Goal True. idtac "END|prosa.classic.model.schedule.uni.service.Service.low_service_implies_existence_of_idle_time". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.service.Service.service_of_jobs_cat_scheduling_interval". Abort.
Check @prosa.classic.model.schedule.uni.service.Service.service_of_jobs_cat_scheduling_interval.
Goal True. idtac "END|prosa.classic.model.schedule.uni.service.Service.service_of_jobs_cat_scheduling_interval". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.service.Service.service_of_jobs_cat_arrival_interval". Abort.
Check @prosa.classic.model.schedule.uni.service.Service.service_of_jobs_cat_arrival_interval.
Goal True. idtac "END|prosa.classic.model.schedule.uni.service.Service.service_of_jobs_cat_arrival_interval". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.service.Service.workload_eq_service_impl_all_jobs_have_completed". Abort.
Check @prosa.classic.model.schedule.uni.service.Service.workload_eq_service_impl_all_jobs_have_completed.
Goal True. idtac "END|prosa.classic.model.schedule.uni.service.Service.workload_eq_service_impl_all_jobs_have_completed". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.service.Service.all_jobs_have_completed_impl_workload_eq_service". Abort.
Check @prosa.classic.model.schedule.uni.service.Service.all_jobs_have_completed_impl_workload_eq_service.
Goal True. idtac "END|prosa.classic.model.schedule.uni.service.Service.all_jobs_have_completed_impl_workload_eq_service". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.schedule.uni.service.Service.all_jobs_have_completed_equiv_workload_eq_service". Abort.
Check @prosa.classic.model.schedule.uni.service.Service.all_jobs_have_completed_equiv_workload_eq_service.
Goal True. idtac "END|prosa.classic.model.schedule.uni.service.Service.all_jobs_have_completed_equiv_workload_eq_service". Abort.
