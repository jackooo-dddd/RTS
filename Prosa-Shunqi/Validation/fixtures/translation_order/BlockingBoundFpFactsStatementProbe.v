Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.BlockingBoundFpFactsSemanticSource.
Import BlockingBoundFpFactsSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.model.schedule.scheduled.
Goal True. idtac "BEGIN|prosa.analysis.facts.blocking_bound.fp.nonpreemptive_segments_bounded_by_blocking". Abort.
Print statement_nonpreemptive_segments_bounded_by_blocking.
Goal True. idtac "END|prosa.analysis.facts.blocking_bound.fp.nonpreemptive_segments_bounded_by_blocking". Abort.
