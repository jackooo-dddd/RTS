Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.RtaIdealFpBoundedNpsSemanticSource.
Import RtaIdealFpBoundedNpsSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.model.schedule.scheduled.
Require Import prosa.model.processor.ideal.
(* display-only: the official elaborated-type evidence was printed with another [processor_state] in scope, so the
   ideal one is displayed as [ideal.processor_state] *)
Module RtaIdealFpBoundedNpsProbeDisplay. Definition processor_state := tt. End RtaIdealFpBoundedNpsProbeDisplay.
Import RtaIdealFpBoundedNpsProbeDisplay.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.fp.bounded_nps.priority_inversion_is_bounded_by_blocking". Abort.
Print statement_priority_inversion_is_bounded_by_blocking.
Goal True. idtac "END|prosa.results.rta.ideal.fp.bounded_nps.priority_inversion_is_bounded_by_blocking". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.fp.bounded_nps.priority_inversion_is_bounded". Abort.
Print statement_priority_inversion_is_bounded.
Goal True. idtac "END|prosa.results.rta.ideal.fp.bounded_nps.priority_inversion_is_bounded". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.fp.bounded_nps.uniprocessor_response_time_bound_fp_with_bounded_nonpreemptive_segments". Abort.
Print statement_uniprocessor_response_time_bound_fp_with_bounded_nonpreemptive_segments.
Goal True. idtac "END|prosa.results.rta.ideal.fp.bounded_nps.uniprocessor_response_time_bound_fp_with_bounded_nonpreemptive_segments". Abort.
