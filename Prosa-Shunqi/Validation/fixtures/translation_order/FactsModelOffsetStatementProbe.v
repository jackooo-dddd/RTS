Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.FactsModelOffsetSemanticSource.
Import FactsModelOffsetSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import prosa.behavior.all prosa.model.task.concept prosa.model.task.arrivals.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.offset.first_job_arrival". Abort.
Print statement_first_job_arrival.
Goal True. idtac "END|prosa.analysis.facts.model.offset.first_job_arrival". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.offset.max_offset_g". Abort.
Print statement_max_offset_g.
Goal True. idtac "END|prosa.analysis.facts.model.offset.max_offset_g". Abort.
