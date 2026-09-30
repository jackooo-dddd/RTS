Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.RtaOvhEdfLimitedPreemptiveSemanticSource.
Import RtaOvhEdfLimitedPreemptiveSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.model.schedule.scheduled.
(* display-only: in the official environment [ideal.processor_state] is also in scope, so the overheads
   processor model prints module-qualified; this shadow reproduces that display (no statement is affected). *)
Module ideal_display. Definition processor_state := tt. End ideal_display. Import ideal_display.
Goal True. idtac "BEGIN|prosa.results.rta.ovh.edf.limited_preemptive.busy_window_recurrence_solution". Abort.
Check @busy_window_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.ovh.edf.limited_preemptive.busy_window_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ovh.edf.limited_preemptive.rta_recurrence_solution". Abort.
Check @rta_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.ovh.edf.limited_preemptive.rta_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ovh.edf.limited_preemptive.uniprocessor_response_time_bound_limited_edf". Abort.
Print statement_uniprocessor_response_time_bound_limited_edf.
Goal True. idtac "END|prosa.results.rta.ovh.edf.limited_preemptive.uniprocessor_response_time_bound_limited_edf". Abort.
