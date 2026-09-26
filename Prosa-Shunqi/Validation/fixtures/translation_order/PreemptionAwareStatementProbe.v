Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.PreemptionAwareSemanticSource.
Import PreemptionAwareSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import prosa.behavior.all prosa.model.processor.ideal.
(* display-only: the official elaborated-type evidence was printed with another
   [processor_state] in scope, so the ideal one is displayed as [ideal.processor_state] *)
Module PreemptionAwareProbeDisplay. Definition processor_state := tt. End PreemptionAwareProbeDisplay.
Import PreemptionAwareProbeDisplay.
Goal True. idtac "BEGIN|prosa.implementation.facts.ideal_uni.preemption_aware.allocation_at_idle". Abort.
Print statement_allocation_at_idle.
Goal True. idtac "END|prosa.implementation.facts.ideal_uni.preemption_aware.allocation_at_idle". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.ideal_uni.preemption_aware.idle_schedule_no_backlogged_jobs". Abort.
Print statement_idle_schedule_no_backlogged_jobs.
Goal True. idtac "END|prosa.implementation.facts.ideal_uni.preemption_aware.idle_schedule_no_backlogged_jobs". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.ideal_uni.preemption_aware.np_schedule_work_conserving". Abort.
Print statement_np_schedule_work_conserving.
Goal True. idtac "END|prosa.implementation.facts.ideal_uni.preemption_aware.np_schedule_work_conserving". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.ideal_uni.preemption_aware.np_schedule_jobs_from_arrival_sequence". Abort.
Print statement_np_schedule_jobs_from_arrival_sequence.
Goal True. idtac "END|prosa.implementation.facts.ideal_uni.preemption_aware.np_schedule_jobs_from_arrival_sequence". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.ideal_uni.preemption_aware.chosen_job_is_ready". Abort.
Print statement_chosen_job_is_ready.
Goal True. idtac "END|prosa.implementation.facts.ideal_uni.preemption_aware.chosen_job_is_ready". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.ideal_uni.preemption_aware.jobs_must_be_ready". Abort.
Print statement_jobs_must_be_ready.
Goal True. idtac "END|prosa.implementation.facts.ideal_uni.preemption_aware.jobs_must_be_ready". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.ideal_uni.preemption_aware.np_schedule_valid". Abort.
Print statement_np_schedule_valid.
Goal True. idtac "END|prosa.implementation.facts.ideal_uni.preemption_aware.np_schedule_valid". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.ideal_uni.preemption_aware.np_job_remains_scheduled". Abort.
Print statement_np_job_remains_scheduled.
Goal True. idtac "END|prosa.implementation.facts.ideal_uni.preemption_aware.np_job_remains_scheduled". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.ideal_uni.preemption_aware.np_consistent". Abort.
Print statement_np_consistent.
Goal True. idtac "END|prosa.implementation.facts.ideal_uni.preemption_aware.np_consistent". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.ideal_uni.preemption_aware.np_respects_preemption_model". Abort.
Print statement_np_respects_preemption_model.
Goal True. idtac "END|prosa.implementation.facts.ideal_uni.preemption_aware.np_respects_preemption_model". Abort.
