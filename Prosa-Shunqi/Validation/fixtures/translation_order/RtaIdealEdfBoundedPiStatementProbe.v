Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.RtaIdealEdfBoundedPiSemanticSource.
Import RtaIdealEdfBoundedPiSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.model.schedule.scheduled.
Require Import prosa.model.processor.ideal.
(* display-only: the official elaborated-type evidence was printed with another [processor_state] in scope, so the
   ideal one is displayed as [ideal.processor_state] *)
Module RtaIdealEdfBoundedPiProbeDisplay. Definition processor_state := tt. End RtaIdealEdfBoundedPiProbeDisplay.
Import RtaIdealEdfBoundedPiProbeDisplay.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.edf.bounded_pi.task_rbf_changes_at". Abort.
Check @task_rbf_changes_at.
Goal True. idtac "END|prosa.results.rta.ideal.edf.bounded_pi.task_rbf_changes_at". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.edf.bounded_pi.bound_on_total_hep_workload_changes_at". Abort.
Check @bound_on_total_hep_workload_changes_at.
Goal True. idtac "END|prosa.results.rta.ideal.edf.bounded_pi.bound_on_total_hep_workload_changes_at". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.edf.bounded_pi.priority_inversion_changes_at". Abort.
Check @priority_inversion_changes_at.
Goal True. idtac "END|prosa.results.rta.ideal.edf.bounded_pi.priority_inversion_changes_at". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.edf.bounded_pi.is_in_search_space". Abort.
Check @is_in_search_space.
Goal True. idtac "END|prosa.results.rta.ideal.edf.bounded_pi.is_in_search_space". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.edf.bounded_pi.instantiated_task_interference_is_bounded". Abort.
Print statement_instantiated_task_interference_is_bounded.
Goal True. idtac "END|prosa.results.rta.ideal.edf.bounded_pi.instantiated_task_interference_is_bounded". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.edf.bounded_pi.A_is_in_concrete_search_space". Abort.
Print statement_A_is_in_concrete_search_space.
Goal True. idtac "END|prosa.results.rta.ideal.edf.bounded_pi.A_is_in_concrete_search_space". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.edf.bounded_pi.correct_search_space". Abort.
Print statement_correct_search_space.
Goal True. idtac "END|prosa.results.rta.ideal.edf.bounded_pi.correct_search_space". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.edf.bounded_pi.uniprocessor_response_time_bound_edf". Abort.
Print statement_uniprocessor_response_time_bound_edf.
Goal True. idtac "END|prosa.results.rta.ideal.edf.bounded_pi.uniprocessor_response_time_bound_edf". Abort.
