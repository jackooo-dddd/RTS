Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.FactsGenericScheduleSemanticSource.
Import FactsGenericScheduleSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import prosa.behavior.all.
Goal True. idtac "BEGIN|prosa.implementation.facts.generic_schedule.schedule_up_to_def". Abort.
Print statement_schedule_up_to_def.
Goal True. idtac "END|prosa.implementation.facts.generic_schedule.schedule_up_to_def". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.generic_schedule.schedule_up_to_unfold". Abort.
Print statement_schedule_up_to_unfold.
Goal True. idtac "END|prosa.implementation.facts.generic_schedule.schedule_up_to_unfold". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.generic_schedule.schedule_up_to_widen". Abort.
Print statement_schedule_up_to_widen.
Goal True. idtac "END|prosa.implementation.facts.generic_schedule.schedule_up_to_widen". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.generic_schedule.schedule_up_to_empty". Abort.
Print statement_schedule_up_to_empty.
Goal True. idtac "END|prosa.implementation.facts.generic_schedule.schedule_up_to_empty". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.generic_schedule.schedule_up_to_prefix_inclusion". Abort.
Print statement_schedule_up_to_prefix_inclusion.
Goal True. idtac "END|prosa.implementation.facts.generic_schedule.schedule_up_to_prefix_inclusion". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.generic_schedule.schedule_up_to_identical_prefix". Abort.
Print statement_schedule_up_to_identical_prefix.
Goal True. idtac "END|prosa.implementation.facts.generic_schedule.schedule_up_to_identical_prefix". Abort.
