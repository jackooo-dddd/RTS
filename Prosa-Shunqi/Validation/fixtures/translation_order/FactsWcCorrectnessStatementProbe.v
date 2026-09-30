Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.FactsWcCorrectnessSemanticSource.
Import FactsWcCorrectnessSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all.
Require Import prosa.model.processor.ideal prosa.model.schedule.work_conserving.
(* display-only: the official elaborated-type evidence was printed with another [processor_state] in scope, so the
   ideal one is displayed as [ideal.processor_state] *)
Module FactsWcCorrectnessProbeDisplay. Definition processor_state := tt. End FactsWcCorrectnessProbeDisplay.
Import FactsWcCorrectnessProbeDisplay.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.is_work_conserving_at". Abort.
Check @is_work_conserving_at.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.is_work_conserving_at". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.swap_candidate_is_in_future". Abort.
Print statement_swap_candidate_is_in_future.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.swap_candidate_is_in_future". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.fsc_respects_has_arrived". Abort.
Print statement_fsc_respects_has_arrived.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.fsc_respects_has_arrived". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.swap_jobs_must_arrive_to_execute". Abort.
Print statement_swap_jobs_must_arrive_to_execute.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.swap_jobs_must_arrive_to_execute". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.fsc_jobs_must_be_ready_to_execute". Abort.
Print statement_fsc_jobs_must_be_ready_to_execute.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.fsc_jobs_must_be_ready_to_execute". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.mwa_service_bound". Abort.
Print statement_mwa_service_bound.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.mwa_service_bound". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.mwa_ready_job_also_ready_in_original_schedule". Abort.
Print statement_mwa_ready_job_also_ready_in_original_schedule.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.mwa_ready_job_also_ready_in_original_schedule". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.max_dl_is_greatest_dl". Abort.
Print statement_max_dl_is_greatest_dl.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.max_dl_is_greatest_dl". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.order". Abort.
Check @order.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.order". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.search_result". Abort.
Check @search_result.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.search_result". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.make_wc_at_case_result_found". Abort.
Print statement_make_wc_at_case_result_found.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.make_wc_at_case_result_found". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.no_relevant_state_in_range". Abort.
Print statement_no_relevant_state_in_range.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.no_relevant_state_in_range". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.service_of_j_is_less_than_cost". Abort.
Print statement_service_of_j_is_less_than_cost.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.service_of_j_is_less_than_cost". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.t_is_less_than_deadline_of_j". Abort.
Print statement_t_is_less_than_deadline_of_j.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.t_is_less_than_deadline_of_j". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.equal_service_t_max_dl". Abort.
Print statement_equal_service_t_max_dl.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.equal_service_t_max_dl". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.j_misses_deadline". Abort.
Print statement_j_misses_deadline.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.j_misses_deadline". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.make_wc_at_case_result_none". Abort.
Print statement_make_wc_at_case_result_none.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.make_wc_at_case_result_none". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.mwa_finds_ready_jobs". Abort.
Print statement_mwa_finds_ready_jobs.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.mwa_finds_ready_jobs". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.mwa_establishes_wc". Abort.
Print statement_mwa_establishes_wc.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.mwa_establishes_wc". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.mwa_jobs_come_from_arrival_sequence". Abort.
Print statement_mwa_jobs_come_from_arrival_sequence.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.mwa_jobs_come_from_arrival_sequence". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.mwa_jobs_must_be_ready_to_execute". Abort.
Print statement_mwa_jobs_must_be_ready_to_execute.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.mwa_jobs_must_be_ready_to_execute". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.mwa_all_deadlines_of_arrivals_met". Abort.
Print statement_mwa_all_deadlines_of_arrivals_met.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.mwa_all_deadlines_of_arrivals_met". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.wc_transform_prefix_inclusion". Abort.
Print statement_wc_transform_prefix_inclusion.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.wc_transform_prefix_inclusion". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.wc_prefix_service_bound". Abort.
Print statement_wc_prefix_service_bound.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.wc_prefix_service_bound". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.wc_prefix_job_meets_deadline". Abort.
Print statement_wc_prefix_job_meets_deadline.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.wc_prefix_job_meets_deadline". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.wc_prefix_jobs_come_from_arrival_sequence". Abort.
Print statement_wc_prefix_jobs_come_from_arrival_sequence.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.wc_prefix_jobs_come_from_arrival_sequence". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.wc_prefix_jobs_must_be_ready_to_execute". Abort.
Print statement_wc_prefix_jobs_must_be_ready_to_execute.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.wc_prefix_jobs_must_be_ready_to_execute". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.wc_jobs_come_from_arrival_sequence". Abort.
Print statement_wc_jobs_come_from_arrival_sequence.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.wc_jobs_come_from_arrival_sequence". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.wc_jobs_must_be_ready_to_execute". Abort.
Print statement_wc_jobs_must_be_ready_to_execute.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.wc_jobs_must_be_ready_to_execute". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.wc_all_deadlines_of_arrivals_met". Abort.
Print statement_wc_all_deadlines_of_arrivals_met.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.wc_all_deadlines_of_arrivals_met". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.wc_is_work_conserving_at". Abort.
Print statement_wc_is_work_conserving_at.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.wc_is_work_conserving_at". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.wc_is_work_conserving". Abort.
Print statement_wc_is_work_conserving.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.wc_is_work_conserving". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.wc_transform_correctness". Abort.
Print statement_wc_transform_correctness.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.wc_transform_correctness". Abort.
