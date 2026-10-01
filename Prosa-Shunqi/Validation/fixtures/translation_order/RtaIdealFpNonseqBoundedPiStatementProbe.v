Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.RtaIdealFpNonseqBoundedPiSemanticSource.
Import RtaIdealFpNonseqBoundedPiSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.model.schedule.scheduled.
Require Import prosa.model.processor.ideal.
(* display-only: the official elaborated-type evidence was printed with another [processor_state] in scope, so the
   ideal one is displayed as [ideal.processor_state] *)
Module RtaIdealFpNonseqBoundedPiProbeDisplay. Definition processor_state := tt. End RtaIdealFpNonseqBoundedPiProbeDisplay.
Import RtaIdealFpNonseqBoundedPiProbeDisplay.
(* display-only: the official elaborated-type evidence was printed with another [is_in_search_space] in scope, so
   the abstract search space is displayed as [search_space.is_in_search_space] *)
Module RtaIdealFpNonseqBoundedPiSearchSpaceDisplay. Definition is_in_search_space := tt. End RtaIdealFpNonseqBoundedPiSearchSpaceDisplay.
Import RtaIdealFpNonseqBoundedPiSearchSpaceDisplay.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.fp.nonseq.bounded_pi.instantiated_busy_intervals_are_bounded". Abort.
Print statement_instantiated_busy_intervals_are_bounded.
Goal True. idtac "END|prosa.results.rta.ideal.fp.nonseq.bounded_pi.instantiated_busy_intervals_are_bounded". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.fp.nonseq.bounded_pi.IBF". Abort.
Check @IBF.
Goal True. idtac "END|prosa.results.rta.ideal.fp.nonseq.bounded_pi.IBF". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.fp.nonseq.bounded_pi.self_intf_bound_case1". Abort.
Print statement_self_intf_bound_case1.
Goal True. idtac "END|prosa.results.rta.ideal.fp.nonseq.bounded_pi.self_intf_bound_case1". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.fp.nonseq.bounded_pi.self_intf_bound_case2". Abort.
Print statement_self_intf_bound_case2.
Goal True. idtac "END|prosa.results.rta.ideal.fp.nonseq.bounded_pi.self_intf_bound_case2". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.fp.nonseq.bounded_pi.self_intf_bound". Abort.
Print statement_self_intf_bound.
Goal True. idtac "END|prosa.results.rta.ideal.fp.nonseq.bounded_pi.self_intf_bound". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.fp.nonseq.bounded_pi.instantiated_task_interference_is_bounded". Abort.
Print statement_instantiated_task_interference_is_bounded.
Goal True. idtac "END|prosa.results.rta.ideal.fp.nonseq.bounded_pi.instantiated_task_interference_is_bounded". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.fp.nonseq.bounded_pi.is_in_concrete_search_space". Abort.
Check @is_in_concrete_search_space.
Goal True. idtac "END|prosa.results.rta.ideal.fp.nonseq.bounded_pi.is_in_concrete_search_space". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.fp.nonseq.bounded_pi.A_is_in_concrete_search_space". Abort.
Print statement_A_is_in_concrete_search_space.
Goal True. idtac "END|prosa.results.rta.ideal.fp.nonseq.bounded_pi.A_is_in_concrete_search_space". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.fp.nonseq.bounded_pi.correct_search_space". Abort.
Print statement_correct_search_space.
Goal True. idtac "END|prosa.results.rta.ideal.fp.nonseq.bounded_pi.correct_search_space". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.fp.nonseq.bounded_pi.uniprocessor_response_time_bound_fp". Abort.
Print statement_uniprocessor_response_time_bound_fp.
Goal True. idtac "END|prosa.results.rta.ideal.fp.nonseq.bounded_pi.uniprocessor_response_time_bound_fp". Abort.
