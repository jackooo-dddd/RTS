Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.FactsEdfOptSemanticSource.
Import FactsEdfOptSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.model.schedule.scheduled.
Require Import prosa.model.processor.ideal prosa.model.schedule.edf.
(* display-only: the official elaborated-type evidence was printed with another [processor_state] and the wc_trans
   [find_swap_candidate] / [relevant_pstate] in scope, so these are displayed qualified *)
Module FactsEdfOptProbeDisplay. Definition processor_state := tt. Definition find_swap_candidate := tt. Definition relevant_pstate := tt. End FactsEdfOptProbeDisplay.
Import FactsEdfOptProbeDisplay.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.t1_relevant". Abort.
Print statement_t1_relevant.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.t1_relevant". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.fsc_search_successful". Abort.
Print statement_fsc_search_successful.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.fsc_search_successful". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.fsc_search_result". Abort.
Print statement_fsc_search_result.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.fsc_search_result". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.fsc_not_idle". Abort.
Print statement_fsc_not_idle.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.fsc_not_idle". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.fsc_found_job_arrival". Abort.
Print statement_fsc_found_job_arrival.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.fsc_found_job_arrival". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.fsc_range". Abort.
Print statement_fsc_range.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.fsc_range". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.fsc_range1". Abort.
Print statement_fsc_range1.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.fsc_range1". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.fsc_found_job_deadline". Abort.
Print statement_fsc_found_job_deadline.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.fsc_found_job_deadline". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.fsc_no_later_deadline". Abort.
Print statement_fsc_no_later_deadline.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.fsc_no_later_deadline". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.scheduled_job_in_sched_has_later_deadline". Abort.
Print statement_scheduled_job_in_sched_has_later_deadline.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.scheduled_job_in_sched_has_later_deadline". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.mea_completed_jobs". Abort.
Print statement_mea_completed_jobs.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.mea_completed_jobs". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.mea_no_deadline_misses". Abort.
Print statement_mea_no_deadline_misses.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.mea_no_deadline_misses". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.mea_scheduled_job_has_later_deadline". Abort.
Print statement_mea_scheduled_job_has_later_deadline.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.mea_scheduled_job_has_later_deadline". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.mea_guarantee_dl_orig". Abort.
Print statement_mea_guarantee_dl_orig.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.mea_guarantee_dl_orig". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.mea_guarantee_fsc_is_j_edf". Abort.
Print statement_mea_guarantee_fsc_is_j_edf.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.mea_guarantee_fsc_is_j_edf". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.mea_guarantee_deadlines". Abort.
Print statement_mea_guarantee_deadlines.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.mea_guarantee_deadlines". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.mea_guarantee_case_t'_past_deadline". Abort.
Print statement_mea_guarantee_case_t'_past_deadline.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.mea_guarantee_case_t'_past_deadline". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.mea_guarantee_case_t'_before_deadline". Abort.
Print statement_mea_guarantee_case_t'_before_deadline.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.mea_guarantee_case_t'_before_deadline". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.make_edf_at_guarantee". Abort.
Print statement_make_edf_at_guarantee.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.make_edf_at_guarantee". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.mea_jobs_must_arrive". Abort.
Print statement_mea_jobs_must_arrive.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.mea_jobs_must_arrive". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.mea_job_scheduled". Abort.
Print statement_mea_job_scheduled.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.mea_job_scheduled". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.mea_job_scheduled'". Abort.
Print statement_mea_job_scheduled'.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.mea_job_scheduled'". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.mea_jobs_come_from_arrival_sequence". Abort.
Print statement_mea_jobs_come_from_arrival_sequence.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.mea_jobs_come_from_arrival_sequence". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.mea_EDF_widen". Abort.
Print statement_mea_EDF_widen.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.mea_EDF_widen". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.edf_prefix_well_formedness". Abort.
Print statement_edf_prefix_well_formedness.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.edf_prefix_well_formedness". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.edf_prefix_jobs_must_arrive". Abort.
Print statement_edf_prefix_jobs_must_arrive.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.edf_prefix_jobs_must_arrive". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.edf_prefix_scheduled_job_has_later_deadline". Abort.
Print statement_edf_prefix_scheduled_job_has_later_deadline.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.edf_prefix_scheduled_job_has_later_deadline". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.edf_prefix_job_scheduled". Abort.
Print statement_edf_prefix_job_scheduled.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.edf_prefix_job_scheduled". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.edf_prefix_job_scheduled'". Abort.
Print statement_edf_prefix_job_scheduled'.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.edf_prefix_job_scheduled'". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.edf_prefix_jobs_come_from_arrival_sequence". Abort.
Print statement_edf_prefix_jobs_come_from_arrival_sequence.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.edf_prefix_jobs_come_from_arrival_sequence". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.edf_prefix_guarantee". Abort.
Print statement_edf_prefix_guarantee.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.edf_prefix_guarantee". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.edf_prefix_inclusion". Abort.
Print statement_edf_prefix_inclusion.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.edf_prefix_inclusion". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.edf_finite_prefix". Abort.
Print statement_edf_finite_prefix.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.edf_finite_prefix". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.edf_transform_ensures_edf". Abort.
Print statement_edf_transform_ensures_edf.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.edf_transform_ensures_edf". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.edf_transform_completed_jobs_dont_execute". Abort.
Print statement_edf_transform_completed_jobs_dont_execute.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.edf_transform_completed_jobs_dont_execute". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.edf_transform_jobs_must_arrive". Abort.
Print statement_edf_transform_jobs_must_arrive.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.edf_transform_jobs_must_arrive". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.edf_transform_deadlines_met". Abort.
Print statement_edf_transform_deadlines_met.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.edf_transform_deadlines_met". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.edf_transform_job_scheduled". Abort.
Print statement_edf_transform_job_scheduled.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.edf_transform_job_scheduled". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.edf_transform_job_scheduled'". Abort.
Print statement_edf_transform_job_scheduled'.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.edf_transform_job_scheduled'". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.edf_transform_jobs_come_from_arrival_sequence". Abort.
Print statement_edf_transform_jobs_come_from_arrival_sequence.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.edf_transform_jobs_come_from_arrival_sequence". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.edf_schedule_is_valid". Abort.
Print statement_edf_schedule_is_valid.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.edf_schedule_is_valid". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.edf_schedule_meets_all_deadlines". Abort.
Print statement_edf_schedule_meets_all_deadlines.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.edf_schedule_meets_all_deadlines". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.edf_schedule_meets_all_deadlines_wrt_arrivals". Abort.
Print statement_edf_schedule_meets_all_deadlines_wrt_arrivals.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.edf_schedule_meets_all_deadlines_wrt_arrivals". Abort.
