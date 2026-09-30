Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.ShiftedJobCostsSemanticSource.
Import ShiftedJobCostsSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all.
Require Import prosa.analysis.definitions.infinite_jobs.
Goal True. idtac "BEGIN|prosa.analysis.facts.shifted_job_costs.job_costs_shifted". Abort.
Check @job_costs_shifted.
Goal True. idtac "END|prosa.analysis.facts.shifted_job_costs.job_costs_shifted". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.shifted_job_costs.job_costs_in_oi". Abort.
Check @job_costs_in_oi.
Goal True. idtac "END|prosa.analysis.facts.shifted_job_costs.job_costs_in_oi". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.shifted_job_costs.job_costs_shifted_valid". Abort.
Print statement_job_costs_shifted_valid.
Goal True. idtac "END|prosa.analysis.facts.shifted_job_costs.job_costs_shifted_valid". Abort.
