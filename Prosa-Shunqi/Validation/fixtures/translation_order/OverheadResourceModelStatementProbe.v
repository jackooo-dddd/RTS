Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.OverheadResourceModelSemanticSource.
Import OverheadResourceModelSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.model.schedule.scheduled.
(* display-only: in the official environment [ideal.processor_state] is also in scope, so the overheads
   processor model prints module-qualified; this shadow reproduces that display (no statement is affected). *)
Module ideal_display. Definition processor_state := tt. End ideal_display. Import ideal_display.
Goal True. idtac "BEGIN|prosa.model.processor.overhead_resource_model.time_spent_in_dispatch". Abort.
Check @time_spent_in_dispatch.
Goal True. idtac "END|prosa.model.processor.overhead_resource_model.time_spent_in_dispatch". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.overhead_resource_model.time_spent_in_context_switch". Abort.
Check @time_spent_in_context_switch.
Goal True. idtac "END|prosa.model.processor.overhead_resource_model.time_spent_in_context_switch". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.overhead_resource_model.time_spent_in_CRPD". Abort.
Check @time_spent_in_CRPD.
Goal True. idtac "END|prosa.model.processor.overhead_resource_model.time_spent_in_CRPD". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.overhead_resource_model.time_spent_in_dispatch_is_bounded_by". Abort.
Check @time_spent_in_dispatch_is_bounded_by.
Goal True. idtac "END|prosa.model.processor.overhead_resource_model.time_spent_in_dispatch_is_bounded_by". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.overhead_resource_model.time_spent_in_context_switch_is_bounded_by". Abort.
Check @time_spent_in_context_switch_is_bounded_by.
Goal True. idtac "END|prosa.model.processor.overhead_resource_model.time_spent_in_context_switch_is_bounded_by". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.overhead_resource_model.time_spent_in_CRPD_is_bounded_by". Abort.
Check @time_spent_in_CRPD_is_bounded_by.
Goal True. idtac "END|prosa.model.processor.overhead_resource_model.time_spent_in_CRPD_is_bounded_by". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.overhead_resource_model.dispatch_precedes_context_switch". Abort.
Check @dispatch_precedes_context_switch.
Goal True. idtac "END|prosa.model.processor.overhead_resource_model.dispatch_precedes_context_switch". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.overhead_resource_model.context_switch_precedes_progress". Abort.
Check @context_switch_precedes_progress.
Goal True. idtac "END|prosa.model.processor.overhead_resource_model.context_switch_precedes_progress". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.overhead_resource_model.context_switch_precedes_CRPD". Abort.
Check @context_switch_precedes_CRPD.
Goal True. idtac "END|prosa.model.processor.overhead_resource_model.context_switch_precedes_CRPD". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.overhead_resource_model.overhead_resource_model". Abort.
Check @overhead_resource_model.
Goal True. idtac "END|prosa.model.processor.overhead_resource_model.overhead_resource_model". Abort.
