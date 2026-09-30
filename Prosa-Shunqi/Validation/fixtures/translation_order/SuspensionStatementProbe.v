Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.SuspensionSemanticSource.
Import SuspensionSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.model.schedule.scheduled.
Goal True. idtac "BEGIN|prosa.model.readiness.suspension.JobSuspension". Abort.
Check @JobSuspension.
Goal True. idtac "END|prosa.model.readiness.suspension.JobSuspension". Abort.
Goal True. idtac "BEGIN|prosa.model.readiness.suspension.suspension_has_passed". Abort.
Check @suspension_has_passed.
Goal True. idtac "END|prosa.model.readiness.suspension.suspension_has_passed". Abort.
Goal True. idtac "BEGIN|prosa.model.readiness.suspension.suspended". Abort.
Check @suspended.
Goal True. idtac "END|prosa.model.readiness.suspension.suspended". Abort.
Goal True. idtac "BEGIN|prosa.model.readiness.suspension.total_suspension". Abort.
Check @total_suspension.
Goal True. idtac "END|prosa.model.readiness.suspension.total_suspension". Abort.
