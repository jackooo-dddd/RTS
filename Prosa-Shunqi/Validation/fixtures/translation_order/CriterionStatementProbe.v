Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.CriterionSemanticSource.
Import CriterionSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
Require Import prosa.behavior.all prosa.model.processor.ideal prosa.model.aggregate.service_of_jobs.
(* display-only: the official elaborated-type evidence was printed with another
   [processor_state] in scope, so the ideal one is displayed as [ideal.processor_state] *)
Module CriterionProbeDisplay. Definition processor_state := tt. End CriterionProbeDisplay.
Import CriterionProbeDisplay.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.schedulability_transferred". Abort.
Check @schedulability_transferred.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.schedulability_transferred". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.deadlines_met". Abort.
Print statement_deadlines_met.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.deadlines_met". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.ref_cost_bounds_online_cost". Abort.
Print statement_ref_cost_bounds_online_cost.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.ref_cost_bounds_online_cost". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.remaining_cost_bound". Abort.
Check @remaining_cost_bound.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.remaining_cost_bound". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.remcost_service". Abort.
Print statement_remcost_service.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.remcost_service". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.remcost_service_during". Abort.
Print statement_remcost_service_during.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.remcost_service_during". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.remcost_total_service_during". Abort.
Print statement_remcost_total_service_during.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.remcost_total_service_during". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.remaining_cost_invariant". Abort.
Print statement_remaining_cost_invariant.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.remaining_cost_invariant". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.online_remaining_cost_bounded". Abort.
Print statement_online_remaining_cost_bounded.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.online_remaining_cost_bounded". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.remaining_cost_positive". Abort.
Print statement_remaining_cost_positive.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.remaining_cost_positive". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.remaining_cost_zero". Abort.
Print statement_remaining_cost_zero.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.remaining_cost_zero". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.critical_jobs". Abort.
Check @critical_jobs.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.critical_jobs". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.critical_jobs_monotonicity". Abort.
Print statement_critical_jobs_monotonicity.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.critical_jobs_monotonicity". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.critical_jobs_dropout". Abort.
Print statement_critical_jobs_dropout.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.critical_jobs_dropout". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.critical_jobs_filter_complete". Abort.
Print statement_critical_jobs_filter_complete.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.critical_jobs_filter_complete". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.critical_jobs_uniq". Abort.
Print statement_critical_jobs_uniq.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.critical_jobs_uniq". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.critical_jobs_min_completion_time". Abort.
Print statement_critical_jobs_min_completion_time.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.critical_jobs_min_completion_time". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.critical_jobs_remaining_cost_monotonic". Abort.
Print statement_critical_jobs_remaining_cost_monotonic.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.critical_jobs_remaining_cost_monotonic". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.slackless_interval". Abort.
Check @slackless_interval.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.slackless_interval". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.contiguously_slackless_interval". Abort.
Check @contiguously_slackless_interval.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.contiguously_slackless_interval". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.transfer_schedulability_criterion". Abort.
Check @transfer_schedulability_criterion.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.transfer_schedulability_criterion". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.late_in_critical_jobs". Abort.
Print statement_late_in_critical_jobs.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.late_in_critical_jobs". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.late_not_at_start". Abort.
Print statement_late_not_at_start.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.late_not_at_start". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.nonpositive_slack". Abort.
Check @nonpositive_slack.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.nonpositive_slack". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.contiguously_nps". Abort.
Check @contiguously_nps.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.contiguously_nps". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.contiguously_nps_start". Abort.
Print statement_contiguously_nps_start.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.contiguously_nps_start". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.contiguously_nps_existence". Abort.
Print statement_contiguously_nps_existence.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.contiguously_nps_existence". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.slackless_interval_step_case_completed_job_rem". Abort.
Print statement_slackless_interval_step_case_completed_job_rem.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.slackless_interval_step_case_completed_job_rem". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.slackless_interval_step_case_completed_job". Abort.
Print statement_slackless_interval_step_case_completed_job.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.slackless_interval_step_case_completed_job". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.slackless_interval_step_case_incomplete_job". Abort.
Print statement_slackless_interval_step_case_incomplete_job.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.slackless_interval_step_case_incomplete_job". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.slackless_interval_step". Abort.
Print statement_slackless_interval_step.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.slackless_interval_step". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.slackless_interval_continuation". Abort.
Print statement_slackless_interval_continuation.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.slackless_interval_continuation". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.slackless_interval_existence". Abort.
Print statement_slackless_interval_existence.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.slackless_interval_existence". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.slackless_interval_completion". Abort.
Print statement_slackless_interval_completion.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.slackless_interval_completion". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.online_transfer_schedulability_criterion_sufficiency". Abort.
Print statement_online_transfer_schedulability_criterion_sufficiency.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.online_transfer_schedulability_criterion_sufficiency". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.online_transfer_schedulability_criterion_ensures_schedulability". Abort.
Print statement_online_transfer_schedulability_criterion_ensures_schedulability.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.online_transfer_schedulability_criterion_ensures_schedulability". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.delay_if_no_critical_job_is_scheduled". Abort.
Print statement_delay_if_no_critical_job_is_scheduled.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.delay_if_no_critical_job_is_scheduled". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.online_transfer_schedulability_criterion_necessity". Abort.
Print statement_online_transfer_schedulability_criterion_necessity.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.online_transfer_schedulability_criterion_necessity". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.ref_transfer_schedulability_criterion_sufficiency". Abort.
Print statement_ref_transfer_schedulability_criterion_sufficiency.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.ref_transfer_schedulability_criterion_sufficiency". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.ref_transfer_schedulability_criterion_ensures_schedulability". Abort.
Print statement_ref_transfer_schedulability_criterion_ensures_schedulability.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.ref_transfer_schedulability_criterion_ensures_schedulability". Abort.
