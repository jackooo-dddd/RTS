Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.RtaIdealFifoBoundedNpsSemanticSource.
Import RtaIdealFifoBoundedNpsSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.model.schedule.scheduled.
Require Import prosa.model.processor.ideal.
(* display-only: the official elaborated-type evidence was printed with another [processor_state] in scope, so the
   ideal one is displayed as [ideal.processor_state] *)
Module RtaIdealFifoBoundedNpsProbeDisplay. Definition processor_state := tt. End RtaIdealFifoBoundedNpsProbeDisplay.
Import RtaIdealFifoBoundedNpsProbeDisplay.
(* display-only: the official elaborated-type evidence was printed with another [is_in_search_space] in scope, so
   the abstract search space is displayed as [search_space.is_in_search_space] *)
Module RtaIdealFifoBoundedNpsSearchSpaceDisplay. Definition is_in_search_space := tt. End RtaIdealFifoBoundedNpsSearchSpaceDisplay.
Import RtaIdealFifoBoundedNpsSearchSpaceDisplay.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.fifo.bounded_nps.abstractly_work_conserving". Abort.
Print statement_abstractly_work_conserving.
Goal True. idtac "END|prosa.results.rta.ideal.fifo.bounded_nps.abstractly_work_conserving". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.fifo.bounded_nps.busy_windows_are_bounded". Abort.
Print statement_busy_windows_are_bounded.
Goal True. idtac "END|prosa.results.rta.ideal.fifo.bounded_nps.busy_windows_are_bounded". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.fifo.bounded_nps.no_priority_inversion". Abort.
Print statement_no_priority_inversion.
Goal True. idtac "END|prosa.results.rta.ideal.fifo.bounded_nps.no_priority_inversion". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.fifo.bounded_nps.IBF_correct". Abort.
Print statement_IBF_correct.
Goal True. idtac "END|prosa.results.rta.ideal.fifo.bounded_nps.IBF_correct". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.fifo.bounded_nps.is_in_concrete_search_space". Abort.
Check @is_in_concrete_search_space.
Goal True. idtac "END|prosa.results.rta.ideal.fifo.bounded_nps.is_in_concrete_search_space". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.fifo.bounded_nps.search_space_refinement". Abort.
Print statement_search_space_refinement.
Goal True. idtac "END|prosa.results.rta.ideal.fifo.bounded_nps.search_space_refinement". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.fifo.bounded_nps.soln_abstract_response_time_recurrence". Abort.
Print statement_soln_abstract_response_time_recurrence.
Goal True. idtac "END|prosa.results.rta.ideal.fifo.bounded_nps.soln_abstract_response_time_recurrence". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.fifo.bounded_nps.uniprocessor_response_time_bound_FIFO". Abort.
Print statement_uniprocessor_response_time_bound_FIFO.
Goal True. idtac "END|prosa.results.rta.ideal.fifo.bounded_nps.uniprocessor_response_time_bound_FIFO". Abort.
