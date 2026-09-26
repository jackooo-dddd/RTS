Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.FactsNonpreemptiveJobSemanticSource.
Import FactsNonpreemptiveJobSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import prosa.model.job.properties prosa.model.schedule.nonpreemptive prosa.model.preemption.fully_nonpreemptive.
Require Import prosa.model.processor.platform_properties.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.job.nonpreemptive.valid_fully_nonpreemptive_model". Abort.
Print statement_valid_fully_nonpreemptive_model.
Goal True. idtac "END|prosa.analysis.facts.preemption.job.nonpreemptive.valid_fully_nonpreemptive_model". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.job.nonpreemptive.job_max_nps_is_job_cost". Abort.
Print statement_job_max_nps_is_job_cost.
Goal True. idtac "END|prosa.analysis.facts.preemption.job.nonpreemptive.job_max_nps_is_job_cost". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.job.nonpreemptive.job_last_nps_is_job_cost". Abort.
Print statement_job_last_nps_is_job_cost.
Goal True. idtac "END|prosa.analysis.facts.preemption.job.nonpreemptive.job_last_nps_is_job_cost". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.job.nonpreemptive.no_preemptions_equiv_nonpreemptive". Abort.
Print statement_no_preemptions_equiv_nonpreemptive.
Goal True. idtac "END|prosa.analysis.facts.preemption.job.nonpreemptive.no_preemptions_equiv_nonpreemptive". Abort.
