Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.ScheduleChangeFactsSemanticSource.
Import ScheduleChangeFactsSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.model.schedule.scheduled.
(* display-only: in the official environment [ideal.processor_state] is also in scope, so the overheads
   processor model prints module-qualified; this shadow reproduces that display (no statement is affected). *)
Module ideal_display. Definition processor_state := tt. End ideal_display. Import ideal_display.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.schedule_change.number_schedule_changes_cat". Abort.
Print statement_number_schedule_changes_cat.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.schedule_change.number_schedule_changes_cat". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.schedule_change.first_schedule_change_exists". Abort.
Print statement_first_schedule_change_exists.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.schedule_change.first_schedule_change_exists". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.schedule_change.number_schedule_changes_widen". Abort.
Print statement_number_schedule_changes_widen.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.schedule_change.number_schedule_changes_widen". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.schedule_change.same_scheduled_state_merge". Abort.
Print statement_same_scheduled_state_merge.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.schedule_change.same_scheduled_state_merge". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.schedule_change.no_schedule_changes_implies_constant_schedule". Abort.
Print statement_no_schedule_changes_implies_constant_schedule.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.schedule_change.no_schedule_changes_implies_constant_schedule". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.schedule_change.no_changes_implies_same_scheduled_job". Abort.
Print statement_no_changes_implies_same_scheduled_job.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.schedule_change.no_changes_implies_same_scheduled_job". Abort.
