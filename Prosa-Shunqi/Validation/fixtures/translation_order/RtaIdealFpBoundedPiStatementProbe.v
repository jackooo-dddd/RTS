Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.RtaIdealFpBoundedPiSemanticSource.
Import RtaIdealFpBoundedPiSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.model.schedule.scheduled.
Require Import prosa.model.processor.ideal.
(* display-only: the official elaborated-type evidence was printed with another [processor_state] in scope, so the
   ideal one is displayed as [ideal.processor_state] *)
Module RtaIdealFpBoundedPiProbeDisplay. Definition processor_state := tt. End RtaIdealFpBoundedPiProbeDisplay.
Import RtaIdealFpBoundedPiProbeDisplay.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.fp.bounded_pi.is_in_search_space". Abort.
Check @is_in_search_space.
Goal True. idtac "END|prosa.results.rta.ideal.fp.bounded_pi.is_in_search_space". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.fp.bounded_pi.instantiated_busy_intervals_are_bounded". Abort.
Print statement_instantiated_busy_intervals_are_bounded.
Goal True. idtac "END|prosa.results.rta.ideal.fp.bounded_pi.instantiated_busy_intervals_are_bounded". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.fp.bounded_pi.instantiated_task_interference_is_bounded". Abort.
Print statement_instantiated_task_interference_is_bounded.
Goal True. idtac "END|prosa.results.rta.ideal.fp.bounded_pi.instantiated_task_interference_is_bounded". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.fp.bounded_pi.A_is_in_concrete_search_space". Abort.
Print statement_A_is_in_concrete_search_space.
Goal True. idtac "END|prosa.results.rta.ideal.fp.bounded_pi.A_is_in_concrete_search_space". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.fp.bounded_pi.correct_search_space". Abort.
Print statement_correct_search_space.
Goal True. idtac "END|prosa.results.rta.ideal.fp.bounded_pi.correct_search_space". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.fp.bounded_pi.uniprocessor_response_time_bound_fp". Abort.
Print statement_uniprocessor_response_time_bound_fp.
Goal True. idtac "END|prosa.results.rta.ideal.fp.bounded_pi.uniprocessor_response_time_bound_fp". Abort.
