Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.DynamicSuspensionSemanticSource.
Import DynamicSuspensionSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.model.schedule.scheduled.
Goal True. idtac "BEGIN|prosa.model.task.suspension.dynamic.TaskTotalSuspension". Abort.
Check @TaskTotalSuspension.
Goal True. idtac "END|prosa.model.task.suspension.dynamic.TaskTotalSuspension". Abort.
Goal True. idtac "BEGIN|prosa.model.task.suspension.dynamic.valid_dynamic_suspensions". Abort.
Check @valid_dynamic_suspensions.
Goal True. idtac "END|prosa.model.task.suspension.dynamic.valid_dynamic_suspensions". Abort.
