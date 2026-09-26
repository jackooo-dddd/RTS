Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.FactsRbfSemanticSource.
Import FactsRbfSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.util.epsilon prosa.util.rel prosa.behavior.all prosa.model.task.concept prosa.model.task.arrivals prosa.model.task.arrival.curves.
Require Import prosa.model.priority.classes prosa.model.job.properties prosa.model.aggregate.workload.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.rbf.task_workload_between_bounded". Abort.
Print statement_task_workload_between_bounded.
Goal True. idtac "END|prosa.analysis.facts.model.rbf.task_workload_between_bounded". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.rbf.rbf_spec". Abort.
Print statement_rbf_spec.
Goal True. idtac "END|prosa.analysis.facts.model.rbf.rbf_spec". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.rbf.rbf_spec'". Abort.
Print statement_rbf_spec'.
Goal True. idtac "END|prosa.analysis.facts.model.rbf.rbf_spec'". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.rbf.total_workload_le_total_rbf". Abort.
Print statement_total_workload_le_total_rbf.
Goal True. idtac "END|prosa.analysis.facts.model.rbf.total_workload_le_total_rbf". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.rbf.workload_of_jobs_bounded". Abort.
Print statement_workload_of_jobs_bounded.
Goal True. idtac "END|prosa.analysis.facts.model.rbf.workload_of_jobs_bounded". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.rbf.athep_workload_le_total_ohep_rbf". Abort.
Print statement_athep_workload_le_total_ohep_rbf.
Goal True. idtac "END|prosa.analysis.facts.model.rbf.athep_workload_le_total_ohep_rbf". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.rbf.hep_workload_le_total_hep_rbf". Abort.
Print statement_hep_workload_le_total_hep_rbf.
Goal True. idtac "END|prosa.analysis.facts.model.rbf.hep_workload_le_total_hep_rbf". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.rbf.hep_workload_le_total_rbf". Abort.
Print statement_hep_workload_le_total_rbf.
Goal True. idtac "END|prosa.analysis.facts.model.rbf.hep_workload_le_total_rbf". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.rbf.task_rbf_0_zero". Abort.
Print statement_task_rbf_0_zero.
Goal True. idtac "END|prosa.analysis.facts.model.rbf.task_rbf_0_zero". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.rbf.task_rbf_monotone". Abort.
Print statement_task_rbf_monotone.
Goal True. idtac "END|prosa.analysis.facts.model.rbf.task_rbf_monotone". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.rbf.task_rbf_1_ge_task_cost". Abort.
Print statement_task_rbf_1_ge_task_cost.
Goal True. idtac "END|prosa.analysis.facts.model.rbf.task_rbf_1_ge_task_cost". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.rbf.task_rbf_ge_task_cost". Abort.
Print statement_task_rbf_ge_task_cost.
Goal True. idtac "END|prosa.analysis.facts.model.rbf.task_rbf_ge_task_cost". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.rbf.task_rbf_epsilon_gt_0". Abort.
Print statement_task_rbf_epsilon_gt_0.
Goal True. idtac "END|prosa.analysis.facts.model.rbf.task_rbf_epsilon_gt_0". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.rbf.task_cost_le_sum_rbf". Abort.
Print statement_task_cost_le_sum_rbf.
Goal True. idtac "END|prosa.analysis.facts.model.rbf.task_cost_le_sum_rbf". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.rbf.total_rbf_monotone". Abort.
Print statement_total_rbf_monotone.
Goal True. idtac "END|prosa.analysis.facts.model.rbf.total_rbf_monotone". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.rbf.total_hep_rbf_monotone". Abort.
Print statement_total_hep_rbf_monotone.
Goal True. idtac "END|prosa.analysis.facts.model.rbf.total_hep_rbf_monotone". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.rbf.total_ohep_rbf_monotone". Abort.
Print statement_total_ohep_rbf_monotone.
Goal True. idtac "END|prosa.analysis.facts.model.rbf.total_ohep_rbf_monotone". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.rbf.pathological_rbf_response_time_bound". Abort.
Print statement_pathological_rbf_response_time_bound.
Goal True. idtac "END|prosa.analysis.facts.model.rbf.pathological_rbf_response_time_bound". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.rbf.pathological_total_hep_rbf_response_time_bound". Abort.
Print statement_pathological_total_hep_rbf_response_time_bound.
Goal True. idtac "END|prosa.analysis.facts.model.rbf.pathological_total_hep_rbf_response_time_bound". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.rbf.pathological_total_hep_rbf_any_bound". Abort.
Print statement_pathological_total_hep_rbf_any_bound.
Goal True. idtac "END|prosa.analysis.facts.model.rbf.pathological_total_hep_rbf_any_bound". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.rbf.hep_rbf_taskwise_partitioning". Abort.
Print statement_hep_rbf_taskwise_partitioning.
Goal True. idtac "END|prosa.analysis.facts.model.rbf.hep_rbf_taskwise_partitioning". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.rbf.split_hep_rbf". Abort.
Print statement_split_hep_rbf.
Goal True. idtac "END|prosa.analysis.facts.model.rbf.split_hep_rbf". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.rbf.split_hep_rbf_weaken". Abort.
Print statement_split_hep_rbf_weaken.
Goal True. idtac "END|prosa.analysis.facts.model.rbf.split_hep_rbf_weaken". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.rbf.total_ohep_rbf0". Abort.
Print statement_total_ohep_rbf0.
Goal True. idtac "END|prosa.analysis.facts.model.rbf.total_ohep_rbf0". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.rbf.ohep_workload_le_rbf". Abort.
Print statement_ohep_workload_le_rbf.
Goal True. idtac "END|prosa.analysis.facts.model.rbf.ohep_workload_le_rbf". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.rbf.task_rbf_without_job_under_analysis_from_arrival". Abort.
Print statement_task_rbf_without_job_under_analysis_from_arrival.
Goal True. idtac "END|prosa.analysis.facts.model.rbf.task_rbf_without_job_under_analysis_from_arrival". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.rbf.task_rbf_without_job_under_analysis". Abort.
Print statement_task_rbf_without_job_under_analysis.
Goal True. idtac "END|prosa.analysis.facts.model.rbf.task_rbf_without_job_under_analysis". Abort.
