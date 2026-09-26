Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.PrioAwareSemanticSource.
Import PrioAwareSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import prosa.behavior.all prosa.model.processor.ideal.
(* display-only: the official elaborated-type evidence was printed with another
   [processor_state] in scope, so the ideal one is displayed as [ideal.processor_state] *)
Module PrioAwareProbeDisplay. Definition processor_state := tt. End PrioAwareProbeDisplay.
Import PrioAwareProbeDisplay.
Goal True. idtac "BEGIN|prosa.implementation.facts.ideal_uni.prio_aware.uni_schedule_work_conserving". Abort.
Print statement_uni_schedule_work_conserving.
Goal True. idtac "END|prosa.implementation.facts.ideal_uni.prio_aware.uni_schedule_work_conserving". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.ideal_uni.prio_aware.uni_schedule_valid". Abort.
Print statement_uni_schedule_valid.
Goal True. idtac "END|prosa.implementation.facts.ideal_uni.prio_aware.uni_schedule_valid". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.ideal_uni.prio_aware.schedule_respects_preemption_model". Abort.
Print statement_schedule_respects_preemption_model.
Goal True. idtac "END|prosa.implementation.facts.ideal_uni.prio_aware.schedule_respects_preemption_model". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.ideal_uni.prio_aware.scheduled_job_is_supremum". Abort.
Print statement_scheduled_job_is_supremum.
Goal True. idtac "END|prosa.implementation.facts.ideal_uni.prio_aware.scheduled_job_is_supremum". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.ideal_uni.prio_aware.schedule_respects_policy". Abort.
Print statement_schedule_respects_policy.
Goal True. idtac "END|prosa.implementation.facts.ideal_uni.prio_aware.schedule_respects_policy". Abort.
