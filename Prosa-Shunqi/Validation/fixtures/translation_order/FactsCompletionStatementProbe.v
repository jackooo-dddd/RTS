Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.FactsCompletionSemanticSource.
Import FactsCompletionSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import prosa.behavior.all prosa.model.processor.platform_properties.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.completion.completion_monotonic". Abort.
Print statement_completion_monotonic.
Goal True. idtac "END|prosa.analysis.facts.behavior.completion.completion_monotonic". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.completion.incompletion_monotonic". Abort.
Print statement_incompletion_monotonic.
Goal True. idtac "END|prosa.analysis.facts.behavior.completion.incompletion_monotonic". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.completion.less_service_than_cost_is_incomplete". Abort.
Print statement_less_service_than_cost_is_incomplete.
Goal True. idtac "END|prosa.analysis.facts.behavior.completion.less_service_than_cost_is_incomplete". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.completion.incomplete_is_positive_remaining_cost". Abort.
Print statement_incomplete_is_positive_remaining_cost.
Goal True. idtac "END|prosa.analysis.facts.behavior.completion.incomplete_is_positive_remaining_cost". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.completion.incomplete_implies_positive_cost". Abort.
Print statement_incomplete_implies_positive_cost.
Goal True. idtac "END|prosa.analysis.facts.behavior.completion.incomplete_implies_positive_cost". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.completion.scheduled_implies_positive_cost". Abort.
Print statement_scheduled_implies_positive_cost.
Goal True. idtac "END|prosa.analysis.facts.behavior.completion.scheduled_implies_positive_cost". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.completion.service_lt_cost". Abort.
Print statement_service_lt_cost.
Goal True. idtac "END|prosa.analysis.facts.behavior.completion.service_lt_cost". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.completion.completed_on_arrival_implies_zero_cost". Abort.
Print statement_completed_on_arrival_implies_zero_cost.
Goal True. idtac "END|prosa.analysis.facts.behavior.completion.completed_on_arrival_implies_zero_cost". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.completion.serviced_implies_positive_remaining_cost". Abort.
Print statement_serviced_implies_positive_remaining_cost.
Goal True. idtac "END|prosa.analysis.facts.behavior.completion.serviced_implies_positive_remaining_cost". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.completion.scheduled_implies_serviced". Abort.
Print statement_scheduled_implies_serviced.
Goal True. idtac "END|prosa.analysis.facts.behavior.completion.scheduled_implies_serviced". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.completion.scheduled_implies_positive_remaining_cost". Abort.
Print statement_scheduled_implies_positive_remaining_cost.
Goal True. idtac "END|prosa.analysis.facts.behavior.completion.scheduled_implies_positive_remaining_cost". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.completion.scheduled_implies_not_completed". Abort.
Print statement_scheduled_implies_not_completed.
Goal True. idtac "END|prosa.analysis.facts.behavior.completion.scheduled_implies_not_completed". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.completion.not_scheduled_remains_incomplete". Abort.
Print statement_not_scheduled_remains_incomplete.
Goal True. idtac "END|prosa.analysis.facts.behavior.completion.not_scheduled_remains_incomplete". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.completion.completed_implies_not_scheduled". Abort.
Print statement_completed_implies_not_scheduled.
Goal True. idtac "END|prosa.analysis.facts.behavior.completion.completed_implies_not_scheduled". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.completion.not_pending_earlier_and_at_0". Abort.
Print statement_not_pending_earlier_and_at_0.
Goal True. idtac "END|prosa.analysis.facts.behavior.completion.not_pending_earlier_and_at_0". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.completion.unit_service". Abort.
Print statement_unit_service.
Goal True. idtac "END|prosa.analysis.facts.behavior.completion.unit_service". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.completion.service_at_most_cost". Abort.
Print statement_service_at_most_cost.
Goal True. idtac "END|prosa.analysis.facts.behavior.completion.service_at_most_cost". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.completion.service_cost_invariant". Abort.
Print statement_service_cost_invariant.
Goal True. idtac "END|prosa.analysis.facts.behavior.completion.service_cost_invariant". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.completion.cumulative_service_le_job_cost". Abort.
Print statement_cumulative_service_le_job_cost.
Goal True. idtac "END|prosa.analysis.facts.behavior.completion.cumulative_service_le_job_cost". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.completion.job_doesnt_complete_before_remaining_cost". Abort.
Print statement_job_doesnt_complete_before_remaining_cost.
Goal True. idtac "END|prosa.analysis.facts.behavior.completion.job_doesnt_complete_before_remaining_cost". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.completion.has_arrived_scheduled". Abort.
Print statement_has_arrived_scheduled.
Goal True. idtac "END|prosa.analysis.facts.behavior.completion.has_arrived_scheduled". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.completion.scheduled_implies_pending". Abort.
Print statement_scheduled_implies_pending.
Goal True. idtac "END|prosa.analysis.facts.behavior.completion.scheduled_implies_pending". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.completion.completed_implies_scheduled_before". Abort.
Print statement_completed_implies_scheduled_before.
Goal True. idtac "END|prosa.analysis.facts.behavior.completion.completed_implies_scheduled_before". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.completion.job_pending_at_arrival". Abort.
Print statement_job_pending_at_arrival.
Goal True. idtac "END|prosa.analysis.facts.behavior.completion.job_pending_at_arrival". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.completion.ready_implies_incomplete". Abort.
Print statement_ready_implies_incomplete.
Goal True. idtac "END|prosa.analysis.facts.behavior.completion.ready_implies_incomplete". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.completion.completed_jobs_are_not_ready". Abort.
Print statement_completed_jobs_are_not_ready.
Goal True. idtac "END|prosa.analysis.facts.behavior.completion.completed_jobs_are_not_ready". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.completion.valid_schedule_implies_completed_jobs_dont_execute". Abort.
Print statement_valid_schedule_implies_completed_jobs_dont_execute.
Goal True. idtac "END|prosa.analysis.facts.behavior.completion.valid_schedule_implies_completed_jobs_dont_execute". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.completion.ideal_progress_completed_jobs". Abort.
Print statement_ideal_progress_completed_jobs.
Goal True. idtac "END|prosa.analysis.facts.behavior.completion.ideal_progress_completed_jobs". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.completion.identical_prefix_completed_by". Abort.
Print statement_identical_prefix_completed_by.
Goal True. idtac "END|prosa.analysis.facts.behavior.completion.identical_prefix_completed_by". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.completion.identical_prefix_pending". Abort.
Print statement_identical_prefix_pending.
Goal True. idtac "END|prosa.analysis.facts.behavior.completion.identical_prefix_pending". Abort.
