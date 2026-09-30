Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.FactsDynamicSuspensionSemanticSource.
Import FactsDynamicSuspensionSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.dynamic_suspension.job_suspension_bounded". Abort.
Print statement_job_suspension_bounded.
Goal True. idtac "END|prosa.analysis.facts.model.dynamic_suspension.job_suspension_bounded". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.dynamic_suspension.suspension_of_task_bounded". Abort.
Print statement_suspension_of_task_bounded.
Goal True. idtac "END|prosa.analysis.facts.model.dynamic_suspension.suspension_of_task_bounded". Abort.
