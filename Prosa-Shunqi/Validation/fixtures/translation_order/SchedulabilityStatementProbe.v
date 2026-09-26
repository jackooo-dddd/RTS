Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.SchedulabilitySemanticSource.
Import SchedulabilitySemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import prosa.behavior.all.
Require Import prosa.model.task.absolute_deadline.
Goal True. idtac "BEGIN|prosa.analysis.definitions.schedulability.task_response_time_bound". Abort.
Check @task_response_time_bound.
Goal True. idtac "END|prosa.analysis.definitions.schedulability.task_response_time_bound". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.schedulability.schedulable_task". Abort.
Check @schedulable_task.
Goal True. idtac "END|prosa.analysis.definitions.schedulability.schedulable_task". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.schedulability.schedulability_from_response_time_bound". Abort.
Print statement_schedulability_from_response_time_bound.
Goal True. idtac "END|prosa.analysis.definitions.schedulability.schedulability_from_response_time_bound". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.schedulability.all_deadlines_met". Abort.
Check @all_deadlines_met.
Goal True. idtac "END|prosa.analysis.definitions.schedulability.all_deadlines_met". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.schedulability.all_deadlines_of_arrivals_met". Abort.
Check @all_deadlines_of_arrivals_met.
Goal True. idtac "END|prosa.analysis.definitions.schedulability.all_deadlines_of_arrivals_met". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.schedulability.all_deadlines_met_in_valid_schedule". Abort.
Print statement_all_deadlines_met_in_valid_schedule.
Goal True. idtac "END|prosa.analysis.definitions.schedulability.all_deadlines_met_in_valid_schedule". Abort.
