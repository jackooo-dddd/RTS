(* Recomputes the authoritative `Check @name` fingerprints for classic/analysis/uni/susp/dynamic/jitter/jitter_schedule_service.v. *)
Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule.
Require Import prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_properties.
Require Import prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.
Require Import prosa.classic.model.arrival.basic.arrival_sequence.
Require Import prosa.classic.model.arrival.basic.job.
Require Import prosa.classic.model.arrival.basic.task.
Require Import prosa.classic.model.arrival.basic.task_arrival.
Require Import prosa.classic.model.arrival.jitter.arrival_sequence.
Require Import prosa.classic.model.arrival.jitter.job.
Require Import prosa.classic.model.priority.
Require Import prosa.classic.model.schedule.uni.jitter.platform.
Require Import prosa.classic.model.schedule.uni.jitter.schedule.
Require Import prosa.classic.model.schedule.uni.jitter.valid_schedule.
Require Import prosa.classic.model.schedule.uni.response_time.
Require Import prosa.classic.model.schedule.uni.schedulability.
Require Import prosa.classic.model.schedule.uni.schedule.
Require Import prosa.classic.model.schedule.uni.service.
Require Import prosa.classic.model.schedule.uni.susp.last_execution.
Require Import prosa.classic.model.schedule.uni.susp.platform.
Require Import prosa.classic.model.schedule.uni.susp.schedule.
Require Import prosa.classic.model.schedule.uni.susp.suspension_intervals.
Require Import prosa.classic.model.schedule.uni.susp.valid_schedule.
Require Import prosa.classic.model.schedule.uni.transformation.construction.
Require Import prosa.classic.model.schedule.uni.workload.
Require Import prosa.classic.model.suspension.
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
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.workload_of_other_hep_jobs_in_sched_susp". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.workload_of_other_hep_jobs_in_sched_susp.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.workload_of_other_hep_jobs_in_sched_susp". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.workload_of_other_hep_jobs_in_sched_jitter". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.workload_of_other_hep_jobs_in_sched_jitter.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.workload_of_other_hep_jobs_in_sched_jitter". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.service_of_other_hep_jobs_in_sched_susp". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.service_of_other_hep_jobs_in_sched_susp.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.service_of_other_hep_jobs_in_sched_susp". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.service_of_other_hep_jobs_in_sched_jitter". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.service_of_other_hep_jobs_in_sched_jitter.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.service_of_other_hep_jobs_in_sched_jitter". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_service_equals_workload_in_jitter". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_service_equals_workload_in_jitter.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_service_equals_workload_in_jitter". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_service_in_sched_susp_le_workload". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_service_in_sched_susp_le_workload.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_service_in_sched_susp_le_workload". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_less_job_service_before_interval_case1". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_less_job_service_before_interval_case1.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_less_job_service_before_interval_case1". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_less_job_service_before_interval_case2". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_less_job_service_before_interval_case2.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_less_job_service_before_interval_case2". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_less_job_service_before_interval_case3". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_less_job_service_before_interval_case3.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_less_job_service_before_interval_case3". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_less_job_service_before_interval_case4". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_less_job_service_before_interval_case4.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_less_job_service_before_interval_case4". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_jitter_equals_R_minus_cost". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_jitter_equals_R_minus_cost.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_jitter_equals_R_minus_cost". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_less_job_service_before_interval_case5". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_less_job_service_before_interval_case5.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_less_job_service_before_interval_case5". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_less_job_service_before_interval". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_less_job_service_before_interval.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_less_job_service_before_interval". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_less_service_before_the_interval". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_less_service_before_the_interval.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_less_service_before_the_interval". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_actual_arrival_before_end_of_interval". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_actual_arrival_before_end_of_interval.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_actual_arrival_before_end_of_interval". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_workload_conservation_inside_interval". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_workload_conservation_inside_interval.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_workload_conservation_inside_interval". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_convert_service_to_workload". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_convert_service_to_workload.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_convert_service_to_workload". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_compare_workload". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_compare_workload.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_compare_workload". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_compare_service". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_compare_service.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_compare_service". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_convert_workload_to_service". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_convert_workload_to_service.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_convert_workload_to_service". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_inductive_step_case1". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_inductive_step_case1.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_inductive_step_case1". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_inductive_step_case2". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_inductive_step_case2.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_inductive_step_case2". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_more_service_inside_the_interval". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_more_service_inside_the_interval.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_more_service_inside_the_interval". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_service_jitter". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_service_jitter.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_service_jitter". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_service_susp". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_service_susp.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_service_susp". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_less_service_for_job_j". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_less_service_for_job_j.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_less_service_for_job_j". Abort.
Goal True. idtac "BEGIN|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_job_j_completes_no_later". Abort.
Check @prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_job_j_completes_no_later.
Goal True. idtac "END|prosa.classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.JitterScheduleService.jitter_reduction_job_j_completes_no_later". Abort.
