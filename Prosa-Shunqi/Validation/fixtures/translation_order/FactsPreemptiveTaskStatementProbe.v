Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.FactsPreemptiveTaskSemanticSource.
Import FactsPreemptiveTaskSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import prosa.util.epsilon.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.task.preemptive.fully_preemptive_model_is_model_with_bounded_nonpreemptive_regions". Abort.
Print statement_fully_preemptive_model_is_model_with_bounded_nonpreemptive_regions.
Goal True. idtac "END|prosa.analysis.facts.preemption.task.preemptive.fully_preemptive_model_is_model_with_bounded_nonpreemptive_regions". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.task.preemptive.fully_preemptive_model_is_valid_model_with_bounded_nonpreemptive_segments". Abort.
Print statement_fully_preemptive_model_is_valid_model_with_bounded_nonpreemptive_segments.
Goal True. idtac "END|prosa.analysis.facts.preemption.task.preemptive.fully_preemptive_model_is_valid_model_with_bounded_nonpreemptive_segments". Abort.
