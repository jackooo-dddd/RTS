Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.RtaIdealElfBoundedPiSemanticSource.
Import RtaIdealElfBoundedPiSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.model.schedule.scheduled.
Require Import prosa.model.processor.ideal.
(* display-only: the official elaborated-type evidence was printed with another [processor_state] in scope, so the
   ideal one is displayed as [ideal.processor_state] *)
Module RtaIdealElfBoundedPiProbeDisplay. Definition processor_state := tt. End RtaIdealElfBoundedPiProbeDisplay.
Import RtaIdealElfBoundedPiProbeDisplay.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.elf.bounded_pi.priority_inversion_bound". Abort.
Check @priority_inversion_bound.
Goal True. idtac "END|prosa.results.rta.ideal.elf.bounded_pi.priority_inversion_bound". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.elf.bounded_pi.priority_inversion_is_bounded". Abort.
Print statement_priority_inversion_is_bounded.
Goal True. idtac "END|prosa.results.rta.ideal.elf.bounded_pi.priority_inversion_is_bounded". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.elf.bounded_pi.instantiated_busy_intervals_are_bounded". Abort.
Print statement_instantiated_busy_intervals_are_bounded.
Goal True. idtac "END|prosa.results.rta.ideal.elf.bounded_pi.instantiated_busy_intervals_are_bounded". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.elf.bounded_pi.total_hp_rbf". Abort.
Check @total_hp_rbf.
Goal True. idtac "END|prosa.results.rta.ideal.elf.bounded_pi.total_hp_rbf". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.elf.bounded_pi.ep_task_intf_interval". Abort.
Check @ep_task_intf_interval.
Goal True. idtac "END|prosa.results.rta.ideal.elf.bounded_pi.ep_task_intf_interval". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.elf.bounded_pi.bound_on_total_ep_workload". Abort.
Check @bound_on_total_ep_workload.
Goal True. idtac "END|prosa.results.rta.ideal.elf.bounded_pi.bound_on_total_ep_workload". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.elf.bounded_pi.task_IBF". Abort.
Check @task_IBF.
Goal True. idtac "END|prosa.results.rta.ideal.elf.bounded_pi.task_IBF". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.elf.bounded_pi.service_of_hp_jobs_from_other_ep_tasks". Abort.
Check @service_of_hp_jobs_from_other_ep_tasks.
Goal True. idtac "END|prosa.results.rta.ideal.elf.bounded_pi.service_of_hp_jobs_from_other_ep_tasks". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.elf.bounded_pi.cumulative_intf_ep_task_service_equiv". Abort.
Print statement_cumulative_intf_ep_task_service_equiv.
Goal True. idtac "END|prosa.results.rta.ideal.elf.bounded_pi.cumulative_intf_ep_task_service_equiv". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.elf.bounded_pi.service_of_hp_jobs_from_other_hp_tasks". Abort.
Check @service_of_hp_jobs_from_other_hp_tasks.
Goal True. idtac "END|prosa.results.rta.ideal.elf.bounded_pi.service_of_hp_jobs_from_other_hp_tasks". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.elf.bounded_pi.cumulative_intf_hp_task_service_equiv". Abort.
Print statement_cumulative_intf_hp_task_service_equiv.
Goal True. idtac "END|prosa.results.rta.ideal.elf.bounded_pi.cumulative_intf_hp_task_service_equiv". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.elf.bounded_pi.total_workload_shorten_range". Abort.
Print statement_total_workload_shorten_range.
Goal True. idtac "END|prosa.results.rta.ideal.elf.bounded_pi.total_workload_shorten_range". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.elf.bounded_pi.bound_on_ep_workload". Abort.
Print statement_bound_on_ep_workload.
Goal True. idtac "END|prosa.results.rta.ideal.elf.bounded_pi.bound_on_ep_workload". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.elf.bounded_pi.bound_on_hp_workload". Abort.
Print statement_bound_on_hp_workload.
Goal True. idtac "END|prosa.results.rta.ideal.elf.bounded_pi.bound_on_hp_workload". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.elf.bounded_pi.instantiated_task_interference_is_bounded". Abort.
Print statement_instantiated_task_interference_is_bounded.
Goal True. idtac "END|prosa.results.rta.ideal.elf.bounded_pi.instantiated_task_interference_is_bounded". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.elf.bounded_pi.task_rbf_changes_at". Abort.
Check @task_rbf_changes_at.
Goal True. idtac "END|prosa.results.rta.ideal.elf.bounded_pi.task_rbf_changes_at". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.elf.bounded_pi.bound_on_total_ep_workload_changes_at". Abort.
Check @bound_on_total_ep_workload_changes_at.
Goal True. idtac "END|prosa.results.rta.ideal.elf.bounded_pi.bound_on_total_ep_workload_changes_at". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.elf.bounded_pi.priority_inversion_changes_at". Abort.
Check @priority_inversion_changes_at.
Goal True. idtac "END|prosa.results.rta.ideal.elf.bounded_pi.priority_inversion_changes_at". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.elf.bounded_pi.is_in_search_space". Abort.
Check @is_in_search_space.
Goal True. idtac "END|prosa.results.rta.ideal.elf.bounded_pi.is_in_search_space". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.elf.bounded_pi.A_is_in_concrete_search_space". Abort.
Print statement_A_is_in_concrete_search_space.
Goal True. idtac "END|prosa.results.rta.ideal.elf.bounded_pi.A_is_in_concrete_search_space". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.elf.bounded_pi.response_time_recurrence_solution_exists". Abort.
Print statement_response_time_recurrence_solution_exists.
Goal True. idtac "END|prosa.results.rta.ideal.elf.bounded_pi.response_time_recurrence_solution_exists". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.elf.bounded_pi.uniprocessor_response_time_bound_elf". Abort.
Print statement_uniprocessor_response_time_bound_elf.
Goal True. idtac "END|prosa.results.rta.ideal.elf.bounded_pi.uniprocessor_response_time_bound_elf". Abort.
