Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.FactsPeriodicArrivalTimesSemanticSource.
Import FactsPeriodicArrivalTimesSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import prosa.behavior.all prosa.model.task.concept prosa.model.task.arrivals.
Goal True. idtac "BEGIN|prosa.analysis.facts.periodic.arrival_times.periodic_arrival_times". Abort.
Print statement_periodic_arrival_times.
Goal True. idtac "END|prosa.analysis.facts.periodic.arrival_times.periodic_arrival_times". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.periodic.arrival_times.job_arrival_times". Abort.
Print statement_job_arrival_times.
Goal True. idtac "END|prosa.analysis.facts.periodic.arrival_times.job_arrival_times". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.periodic.arrival_times.job_arr_index". Abort.
Print statement_job_arr_index.
Goal True. idtac "END|prosa.analysis.facts.periodic.arrival_times.job_arr_index". Abort.
