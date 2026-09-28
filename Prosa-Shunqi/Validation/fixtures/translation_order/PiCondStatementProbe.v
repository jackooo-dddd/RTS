Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.PiCondSemanticSource.
Import PiCondSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.model.schedule.scheduled.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.pi_cond.cum_task_pi_eq". Abort.
Print statement_cum_task_pi_eq.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.pi_cond.cum_task_pi_eq". Abort.
