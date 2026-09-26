Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.PeriodicAsSporadicSemanticSource.
Import PeriodicAsSporadicSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import prosa.behavior.all prosa.model.task.concept prosa.model.task.arrivals prosa.model.task.arrival.sporadic.
Goal True. idtac "BEGIN|prosa.model.task.arrival.periodic_as_sporadic.periodic_as_sporadic". Abort.
Check @periodic_as_sporadic.
Goal True. idtac "END|prosa.model.task.arrival.periodic_as_sporadic.periodic_as_sporadic". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.periodic_as_sporadic.valid_period_is_valid_inter_arrival_time". Abort.
Print statement_valid_period_is_valid_inter_arrival_time.
Goal True. idtac "END|prosa.model.task.arrival.periodic_as_sporadic.valid_period_is_valid_inter_arrival_time". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.periodic_as_sporadic.periodic_task_respects_sporadic_task_model". Abort.
Print statement_periodic_task_respects_sporadic_task_model.
Goal True. idtac "END|prosa.model.task.arrival.periodic_as_sporadic.periodic_task_respects_sporadic_task_model". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.periodic_as_sporadic.valid_periods_are_valid_inter_arrival_times". Abort.
Print statement_valid_periods_are_valid_inter_arrival_times.
Goal True. idtac "END|prosa.model.task.arrival.periodic_as_sporadic.valid_periods_are_valid_inter_arrival_times". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.periodic_as_sporadic.periodic_task_sets_respect_sporadic_task_model". Abort.
Print statement_periodic_task_sets_respect_sporadic_task_model.
Goal True. idtac "END|prosa.model.task.arrival.periodic_as_sporadic.periodic_task_sets_respect_sporadic_task_model". Abort.
