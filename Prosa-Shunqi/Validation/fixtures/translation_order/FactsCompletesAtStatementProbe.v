Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.FactsCompletesAtSemanticSource.
Import FactsCompletesAtSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all.
Goal True. idtac "BEGIN|prosa.analysis.facts.completes_at.scheduled_at_precedes_completes_at". Abort.
Print statement_scheduled_at_precedes_completes_at.
Goal True. idtac "END|prosa.analysis.facts.completes_at.scheduled_at_precedes_completes_at". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.completes_at.job_completes_at_most_once". Abort.
Print statement_job_completes_at_most_once.
Goal True. idtac "END|prosa.analysis.facts.completes_at.job_completes_at_most_once". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.completes_at.only_one_job_completes_at_a_time". Abort.
Print statement_only_one_job_completes_at_a_time.
Goal True. idtac "END|prosa.analysis.facts.completes_at.only_one_job_completes_at_a_time". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.completes_at.completetion_time_is_preemption_time". Abort.
Print statement_completetion_time_is_preemption_time.
Goal True. idtac "END|prosa.analysis.facts.completes_at.completetion_time_is_preemption_time". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.completes_at.no_early_hep_job_completes_during_busy_prefix". Abort.
Print statement_no_early_hep_job_completes_during_busy_prefix.
Goal True. idtac "END|prosa.analysis.facts.completes_at.no_early_hep_job_completes_during_busy_prefix". Abort.
