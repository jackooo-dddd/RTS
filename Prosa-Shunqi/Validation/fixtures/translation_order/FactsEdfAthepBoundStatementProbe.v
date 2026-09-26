Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.FactsEdfAthepBoundSemanticSource.
Import FactsEdfAthepBoundSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.util.epsilon prosa.util.rel prosa.behavior.all prosa.model.task.concept prosa.model.task.arrival.curves.
Require Import prosa.model.priority.classes prosa.model.priority.edf prosa.model.task.absolute_deadline prosa.model.job.properties prosa.model.aggregate.workload.
Goal True. idtac "BEGIN|prosa.analysis.facts.workload.edf_athep_bound.total_workload_shorten_range". Abort.
Print statement_total_workload_shorten_range.
Goal True. idtac "END|prosa.analysis.facts.workload.edf_athep_bound.total_workload_shorten_range". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.workload.edf_athep_bound.sum_of_workloads_is_at_most_bound_on_total_hep_workload". Abort.
Print statement_sum_of_workloads_is_at_most_bound_on_total_hep_workload.
Goal True. idtac "END|prosa.analysis.facts.workload.edf_athep_bound.sum_of_workloads_is_at_most_bound_on_total_hep_workload". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.workload.edf_athep_bound.bound_on_athep_workload_is_valid". Abort.
Print statement_bound_on_athep_workload_is_valid.
Goal True. idtac "END|prosa.analysis.facts.workload.edf_athep_bound.bound_on_athep_workload_is_valid". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.workload.edf_athep_bound.bound_on_athep_workload_monotone". Abort.
Print statement_bound_on_athep_workload_monotone.
Goal True. idtac "END|prosa.analysis.facts.workload.edf_athep_bound.bound_on_athep_workload_monotone". Abort.
