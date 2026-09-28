Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.BusyIntervalArrivalSemanticSource.
Import BusyIntervalArrivalSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import prosa.behavior.all.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.arrival.busy_interval_prefix_job_arrival". Abort.
Print statement_busy_interval_prefix_job_arrival.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.arrival.busy_interval_prefix_job_arrival". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.arrival.busy_interval_job_arrival". Abort.
Print statement_busy_interval_job_arrival.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.arrival.busy_interval_job_arrival". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.arrival.busy_prefix_starts_when_hep_job_arrives". Abort.
Print statement_busy_prefix_starts_when_hep_job_arrives.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.arrival.busy_prefix_starts_when_hep_job_arrives". Abort.
