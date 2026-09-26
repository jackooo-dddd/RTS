Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.IdealUniSchedulerSemanticSource.
Import IdealUniSchedulerSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import prosa.behavior.all prosa.model.processor.ideal.
(* display-only: the official elaborated-type evidence was printed with another
   [processor_state] in scope, so the ideal one is displayed as [ideal.processor_state] *)
Module IdealUniSchedulerProbeDisplay. Definition processor_state := tt. End IdealUniSchedulerProbeDisplay.
Import IdealUniSchedulerProbeDisplay.
Goal True. idtac "BEGIN|prosa.implementation.definitions.ideal_uni_scheduler.prev_job_nonpreemptive". Abort.
Check @prev_job_nonpreemptive.
Goal True. idtac "END|prosa.implementation.definitions.ideal_uni_scheduler.prev_job_nonpreemptive". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.ideal_uni_scheduler.allocation_at". Abort.
Check @allocation_at.
Goal True. idtac "END|prosa.implementation.definitions.ideal_uni_scheduler.allocation_at". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.ideal_uni_scheduler.pmc_uni_schedule". Abort.
Check @pmc_uni_schedule.
Goal True. idtac "END|prosa.implementation.definitions.ideal_uni_scheduler.pmc_uni_schedule". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.ideal_uni_scheduler.choose_highest_prio_job". Abort.
Check @choose_highest_prio_job.
Goal True. idtac "END|prosa.implementation.definitions.ideal_uni_scheduler.choose_highest_prio_job". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.ideal_uni_scheduler.uni_schedule". Abort.
Check @uni_schedule.
Goal True. idtac "END|prosa.implementation.definitions.ideal_uni_scheduler.uni_schedule". Abort.
