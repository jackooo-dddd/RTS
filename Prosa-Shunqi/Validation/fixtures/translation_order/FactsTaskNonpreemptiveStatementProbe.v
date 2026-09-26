Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.FactsTaskNonpreemptiveSemanticSource.
Import FactsTaskNonpreemptiveSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import prosa.util.epsilon.
Require Import prosa.model.processor.platform_properties prosa.model.schedule.nonpreemptive prosa.model.preemption.fully_nonpreemptive.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.task.nonpreemptive.fully_nonpreemptive_model_is_model_with_bounded_nonpreemptive_regions". Abort.
Print statement_fully_nonpreemptive_model_is_model_with_bounded_nonpreemptive_regions.
Goal True. idtac "END|prosa.analysis.facts.preemption.task.nonpreemptive.fully_nonpreemptive_model_is_model_with_bounded_nonpreemptive_regions". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.task.nonpreemptive.fully_nonpreemptive_model_is_valid_model_with_bounded_nonpreemptive_regions". Abort.
Print statement_fully_nonpreemptive_model_is_valid_model_with_bounded_nonpreemptive_regions.
Goal True. idtac "END|prosa.analysis.facts.preemption.task.nonpreemptive.fully_nonpreemptive_model_is_valid_model_with_bounded_nonpreemptive_regions". Abort.
