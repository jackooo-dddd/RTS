Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.FactsRtcNonpreemptiveSemanticSource.
Import FactsRtcNonpreemptiveSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import prosa.util.epsilon.
Require Import prosa.model.processor.platform_properties prosa.model.schedule.nonpreemptive prosa.model.preemption.fully_nonpreemptive.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.rtc_threshold.nonpreemptive.job_rtc_threshold_is_0". Abort.
Print statement_job_rtc_threshold_is_0.
Goal True. idtac "END|prosa.analysis.facts.preemption.rtc_threshold.nonpreemptive.job_rtc_threshold_is_0". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.rtc_threshold.nonpreemptive.job_rtc_threshold_is_ε". Abort.
Print statement_job_rtc_threshold_is_ε.
Goal True. idtac "END|prosa.analysis.facts.preemption.rtc_threshold.nonpreemptive.job_rtc_threshold_is_ε". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.rtc_threshold.nonpreemptive.fully_nonpreemptive_valid_task_run_to_completion_threshold". Abort.
Print statement_fully_nonpreemptive_valid_task_run_to_completion_threshold.
Goal True. idtac "END|prosa.analysis.facts.preemption.rtc_threshold.nonpreemptive.fully_nonpreemptive_valid_task_run_to_completion_threshold". Abort.
