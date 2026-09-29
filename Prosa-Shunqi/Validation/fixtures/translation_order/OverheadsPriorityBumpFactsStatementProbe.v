Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.PriorityBumpFactsSemanticSource.
Import PriorityBumpFactsSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.model.schedule.scheduled.
(* display-only: in the official environment [ideal.processor_state] is also in scope, so the overheads
   processor model prints module-qualified; this shadow reproduces that display (no statement is affected). *)
Module ideal_display. Definition processor_state := tt. End ideal_display. Import ideal_display.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.priority_bump.priority_bump_implies_preemption_time". Abort.
Print statement_priority_bump_implies_preemption_time.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.priority_bump.priority_bump_implies_preemption_time". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.priority_bump.priority_bump_implies_hp_arrival_in_prefix". Abort.
Print statement_priority_bump_implies_hp_arrival_in_prefix.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.priority_bump.priority_bump_implies_hp_arrival_in_prefix". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.priority_bump.no_priority_bumps_in_fifo". Abort.
Print statement_no_priority_bumps_in_fifo.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.priority_bump.no_priority_bumps_in_fifo". Abort.
