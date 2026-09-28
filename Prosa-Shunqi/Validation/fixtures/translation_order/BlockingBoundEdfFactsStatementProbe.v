Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.BlockingBoundEdfFactsSemanticSource.
Import BlockingBoundEdfFactsSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.model.schedule.scheduled.
Require Import prosa.model.priority.edf prosa.model.task.absolute_deadline prosa.model.task.arrival.curves.
Goal True. idtac "BEGIN|prosa.analysis.facts.blocking_bound.edf.nonpreemptive_segments_bounded_by_blocking". Abort.
Print statement_nonpreemptive_segments_bounded_by_blocking.
Goal True. idtac "END|prosa.analysis.facts.blocking_bound.edf.nonpreemptive_segments_bounded_by_blocking". Abort.
