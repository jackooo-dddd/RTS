Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.FactsPeriodicArrivalSeparationSemanticSource.
Import FactsPeriodicArrivalSeparationSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import prosa.behavior.all prosa.model.task.concept prosa.model.task.arrivals.
Goal True. idtac "BEGIN|prosa.analysis.facts.periodic.arrival_separation.consecutive_job_separation". Abort.
Print statement_consecutive_job_separation.
Goal True. idtac "END|prosa.analysis.facts.periodic.arrival_separation.consecutive_job_separation". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.periodic.arrival_separation.job_arrival_separation_when_index_diff_is_k". Abort.
Print statement_job_arrival_separation_when_index_diff_is_k.
Goal True. idtac "END|prosa.analysis.facts.periodic.arrival_separation.job_arrival_separation_when_index_diff_is_k". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.periodic.arrival_separation.job_sep_periodic". Abort.
Print statement_job_sep_periodic.
Goal True. idtac "END|prosa.analysis.facts.periodic.arrival_separation.job_sep_periodic". Abort.
