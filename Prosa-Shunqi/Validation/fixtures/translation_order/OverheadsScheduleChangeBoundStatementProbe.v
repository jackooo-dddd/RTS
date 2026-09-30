Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.ScheduleChangeBoundSemanticSource.
Import ScheduleChangeBoundSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.model.schedule.scheduled.
(* display-only: in the official environment [ideal.processor_state] is also in scope, so the overheads
   processor model prints module-qualified; this shadow reproduces that display (no statement is affected). *)
Module ideal_display. Definition processor_state := tt. End ideal_display. Import ideal_display.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.schedule_change_bound.schedule_changes_bounded_by_total_arrivals_JLFP". Abort.
Print statement_schedule_changes_bounded_by_total_arrivals_JLFP.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.schedule_change_bound.schedule_changes_bounded_by_total_arrivals_JLFP". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.schedule_change_bound.schedule_changes_bounded_by_total_arrivals_FP". Abort.
Print statement_schedule_changes_bounded_by_total_arrivals_FP.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.schedule_change_bound.schedule_changes_bounded_by_total_arrivals_FP". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.schedule_change_bound.schedule_changes_bounded_by_total_arrivals_FIFO". Abort.
Print statement_schedule_changes_bounded_by_total_arrivals_FIFO.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.schedule_change_bound.schedule_changes_bounded_by_total_arrivals_FIFO". Abort.
