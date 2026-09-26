Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.PeriodicSemanticSource.
Import PeriodicSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import prosa.behavior.all prosa.model.task.concept prosa.model.task.arrivals.
Goal True. idtac "BEGIN|prosa.model.task.arrival.periodic.PeriodicModel". Abort.
Check @PeriodicModel.
Goal True. idtac "END|prosa.model.task.arrival.periodic.PeriodicModel". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.periodic.valid_period". Abort.
Check @valid_period.
Goal True. idtac "END|prosa.model.task.arrival.periodic.valid_period". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.periodic.respects_periodic_task_model". Abort.
Check @respects_periodic_task_model.
Goal True. idtac "END|prosa.model.task.arrival.periodic.respects_periodic_task_model". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.periodic.valid_periods". Abort.
Check @valid_periods.
Goal True. idtac "END|prosa.model.task.arrival.periodic.valid_periods". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.periodic.taskset_respects_periodic_task_model". Abort.
Check @taskset_respects_periodic_task_model.
Goal True. idtac "END|prosa.model.task.arrival.periodic.taskset_respects_periodic_task_model". Abort.
