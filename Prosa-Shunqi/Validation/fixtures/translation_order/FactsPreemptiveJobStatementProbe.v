Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.FactsPreemptiveJobSemanticSource.
Import FactsPreemptiveJobSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import prosa.util.epsilon.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.job.preemptive.valid_fully_preemptive_model". Abort.
Print statement_valid_fully_preemptive_model.
Goal True. idtac "END|prosa.analysis.facts.preemption.job.preemptive.valid_fully_preemptive_model". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.job.preemptive.job_max_nps_is_0". Abort.
Print statement_job_max_nps_is_0.
Goal True. idtac "END|prosa.analysis.facts.preemption.job.preemptive.job_max_nps_is_0". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.job.preemptive.job_max_nps_is_ε". Abort.
Print statement_job_max_nps_is_ε.
Goal True. idtac "END|prosa.analysis.facts.preemption.job.preemptive.job_max_nps_is_ε". Abort.
