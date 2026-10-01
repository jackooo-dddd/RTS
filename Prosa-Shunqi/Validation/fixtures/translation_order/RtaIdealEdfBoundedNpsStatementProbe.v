Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.RtaIdealEdfBoundedNpsSemanticSource.
Import RtaIdealEdfBoundedNpsSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.model.schedule.scheduled.
Require Import prosa.model.processor.ideal.
(* display-only: the official elaborated-type evidence was printed with another [processor_state] in scope, so the
   ideal one is displayed as [ideal.processor_state] *)
Module RtaIdealEdfBoundedNpsProbeDisplay. Definition processor_state := tt. End RtaIdealEdfBoundedNpsProbeDisplay.
Import RtaIdealEdfBoundedNpsProbeDisplay.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.edf.bounded_nps.is_in_search_space". Abort.
Check @is_in_search_space.
Goal True. idtac "END|prosa.results.rta.ideal.edf.bounded_nps.is_in_search_space". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.edf.bounded_nps.blocking_bound_decreasing". Abort.
Print statement_blocking_bound_decreasing.
Goal True. idtac "END|prosa.results.rta.ideal.edf.bounded_nps.blocking_bound_decreasing". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.edf.bounded_nps.task_with_equal_deadline_exists". Abort.
Print statement_task_with_equal_deadline_exists.
Goal True. idtac "END|prosa.results.rta.ideal.edf.bounded_nps.task_with_equal_deadline_exists". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.edf.bounded_nps.search_space_inclusion". Abort.
Print statement_search_space_inclusion.
Goal True. idtac "END|prosa.results.rta.ideal.edf.bounded_nps.search_space_inclusion". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.edf.bounded_nps.uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments". Abort.
Print statement_uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments.
Goal True. idtac "END|prosa.results.rta.ideal.edf.bounded_nps.uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments". Abort.
