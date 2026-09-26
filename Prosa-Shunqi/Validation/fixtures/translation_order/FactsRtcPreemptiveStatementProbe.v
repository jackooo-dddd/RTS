Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.FactsRtcPreemptiveSemanticSource.
Import FactsRtcPreemptiveSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import prosa.util.epsilon.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.rtc_threshold.preemptive.fully_preemptive_valid_task_run_to_completion_threshold". Abort.
Print statement_fully_preemptive_valid_task_run_to_completion_threshold.
Goal True. idtac "END|prosa.analysis.facts.preemption.rtc_threshold.preemptive.fully_preemptive_valid_task_run_to_completion_threshold". Abort.
