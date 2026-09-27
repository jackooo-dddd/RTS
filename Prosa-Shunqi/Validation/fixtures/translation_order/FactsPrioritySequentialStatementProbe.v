Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.FactsPrioritySequentialSemanticSource.
Import FactsPrioritySequentialSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import prosa.behavior.all.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.sequential.early_hep_job_is_scheduled". Abort.
Print statement_early_hep_job_is_scheduled.
Goal True. idtac "END|prosa.analysis.facts.priority.sequential.early_hep_job_is_scheduled". Abort.
