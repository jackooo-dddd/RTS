Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.FactsSporadicArrivalTimesSemanticSource.
Import FactsSporadicArrivalTimesSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import prosa.model.task.arrivals.
Require Import prosa.model.task.arrival.sporadic.
Goal True. idtac "BEGIN|prosa.analysis.facts.sporadic.arrival_times.lower_index_implies_earlier_arrival". Abort.
Print statement_lower_index_implies_earlier_arrival.
Goal True. idtac "END|prosa.analysis.facts.sporadic.arrival_times.lower_index_implies_earlier_arrival". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.sporadic.arrival_times.same_jobs_iff_same_arr". Abort.
Print statement_same_jobs_iff_same_arr.
Goal True. idtac "END|prosa.analysis.facts.sporadic.arrival_times.same_jobs_iff_same_arr". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.sporadic.arrival_times.uneq_job_uneq_arr". Abort.
Print statement_uneq_job_uneq_arr.
Goal True. idtac "END|prosa.analysis.facts.sporadic.arrival_times.uneq_job_uneq_arr". Abort.
