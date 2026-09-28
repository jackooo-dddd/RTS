Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.FactsModelSequentialSemanticSource.
Import FactsModelSequentialSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all.
Require Import prosa.model.task.sequentiality prosa.analysis.definitions.readiness.
Module ReadinessDisplay. Definition sequential_readiness := tt. End ReadinessDisplay. Import ReadinessDisplay.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.sequential.scheduler_executes_job_with_earliest_arrival". Abort.
Print statement_scheduler_executes_job_with_earliest_arrival.
Goal True. idtac "END|prosa.analysis.facts.model.sequential.scheduler_executes_job_with_earliest_arrival". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.sequential.sequential_tasks_different_tasks". Abort.
Print statement_sequential_tasks_different_tasks.
Goal True. idtac "END|prosa.analysis.facts.model.sequential.sequential_tasks_different_tasks". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.sequential.sequential_tasks_from_readiness". Abort.
Print statement_sequential_tasks_from_readiness.
Goal True. idtac "END|prosa.analysis.facts.model.sequential.sequential_tasks_from_readiness". Abort.
