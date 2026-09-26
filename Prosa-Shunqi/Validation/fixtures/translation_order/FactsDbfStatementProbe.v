Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.FactsDbfSemanticSource.
Import FactsDbfSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.model.task.concept prosa.model.task.arrivals prosa.model.task.arrival.curves prosa.model.aggregate.workload.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.dbf.task_demand_within". Abort.
Check @task_demand_within.
Goal True. idtac "END|prosa.analysis.facts.model.dbf.task_demand_within". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.dbf.total_demand_within". Abort.
Check @total_demand_within.
Goal True. idtac "END|prosa.analysis.facts.model.dbf.total_demand_within". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.dbf.task_arrivals_with_deadline_within_eq". Abort.
Print statement_task_arrivals_with_deadline_within_eq.
Goal True. idtac "END|prosa.analysis.facts.model.dbf.task_arrivals_with_deadline_within_eq". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.dbf.num_task_arrivals_with_deadline_within_eq". Abort.
Print statement_num_task_arrivals_with_deadline_within_eq.
Goal True. idtac "END|prosa.analysis.facts.model.dbf.num_task_arrivals_with_deadline_within_eq". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.dbf.task_demand_within_le_task_dbf". Abort.
Print statement_task_demand_within_le_task_dbf.
Goal True. idtac "END|prosa.analysis.facts.model.dbf.task_demand_within_le_task_dbf". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.dbf.task_demand_within_le_task_rbf_shifted". Abort.
Print statement_task_demand_within_le_task_rbf_shifted.
Goal True. idtac "END|prosa.analysis.facts.model.dbf.task_demand_within_le_task_rbf_shifted". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.dbf.total_demand_within_le_total_dbf". Abort.
Print statement_total_demand_within_le_total_dbf.
Goal True. idtac "END|prosa.analysis.facts.model.dbf.total_demand_within_le_total_dbf". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.dbf.total_demand_within_le_sum_task_rbf_shifted". Abort.
Print statement_total_demand_within_le_sum_task_rbf_shifted.
Goal True. idtac "END|prosa.analysis.facts.model.dbf.total_demand_within_le_sum_task_rbf_shifted". Abort.
