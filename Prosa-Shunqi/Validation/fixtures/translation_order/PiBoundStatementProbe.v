Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.PiBoundSemanticSource.
Import PiBoundSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.model.schedule.scheduled.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.pi_bound.priority_inversion_is_bounded". Abort.
Print statement_priority_inversion_is_bounded.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.pi_bound.priority_inversion_is_bounded". Abort.
