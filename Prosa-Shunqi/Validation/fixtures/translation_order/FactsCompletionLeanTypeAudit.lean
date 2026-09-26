import Prosa.Analysis.Facts.Behavior.Completion
set_option pp.fieldNotation false

#check @Prosa.Analysis.Facts.Behavior.Completion.completion_monotonic
#check @Prosa.Analysis.Facts.Behavior.Completion.incompletion_monotonic
#check @Prosa.Analysis.Facts.Behavior.Completion.less_service_than_cost_is_incomplete
#check @Prosa.Analysis.Facts.Behavior.Completion.incomplete_is_positive_remaining_cost
#check @Prosa.Analysis.Facts.Behavior.Completion.incomplete_implies_positive_cost
#check @Prosa.Analysis.Facts.Behavior.Completion.scheduled_implies_positive_cost
#check @Prosa.Analysis.Facts.Behavior.Completion.service_lt_cost
#check @Prosa.Analysis.Facts.Behavior.Completion.completed_on_arrival_implies_zero_cost
#check @Prosa.Analysis.Facts.Behavior.Completion.serviced_implies_positive_remaining_cost
#check @Prosa.Analysis.Facts.Behavior.Completion.scheduled_implies_serviced
#check @Prosa.Analysis.Facts.Behavior.Completion.scheduled_implies_positive_remaining_cost
#check @Prosa.Analysis.Facts.Behavior.Completion.scheduled_implies_not_completed
#check @Prosa.Analysis.Facts.Behavior.Completion.not_scheduled_remains_incomplete
#check @Prosa.Analysis.Facts.Behavior.Completion.completed_implies_not_scheduled
#check @Prosa.Analysis.Facts.Behavior.Completion.not_pending_earlier_and_at_0
#check @Prosa.Analysis.Facts.Behavior.Completion.unit_service
#check @Prosa.Analysis.Facts.Behavior.Completion.service_at_most_cost
#check @Prosa.Analysis.Facts.Behavior.Completion.service_cost_invariant
#check @Prosa.Analysis.Facts.Behavior.Completion.cumulative_service_le_job_cost
#check @Prosa.Analysis.Facts.Behavior.Completion.job_doesnt_complete_before_remaining_cost
#check @Prosa.Analysis.Facts.Behavior.Completion.has_arrived_scheduled
#check @Prosa.Analysis.Facts.Behavior.Completion.scheduled_implies_pending
#check @Prosa.Analysis.Facts.Behavior.Completion.completed_implies_scheduled_before
#check @Prosa.Analysis.Facts.Behavior.Completion.job_pending_at_arrival
#check @Prosa.Analysis.Facts.Behavior.Completion.ready_implies_incomplete
#check @Prosa.Analysis.Facts.Behavior.Completion.completed_jobs_are_not_ready
#check @Prosa.Analysis.Facts.Behavior.Completion.valid_schedule_implies_completed_jobs_dont_execute
#check @Prosa.Analysis.Facts.Behavior.Completion.ideal_progress_completed_jobs
#check @Prosa.Analysis.Facts.Behavior.Completion.identical_prefix_completed_by
#check @Prosa.Analysis.Facts.Behavior.Completion.identical_prefix_pending

#print axioms Prosa.Analysis.Facts.Behavior.Completion.completion_monotonic
#print axioms Prosa.Analysis.Facts.Behavior.Completion.incompletion_monotonic
#print axioms Prosa.Analysis.Facts.Behavior.Completion.less_service_than_cost_is_incomplete
#print axioms Prosa.Analysis.Facts.Behavior.Completion.incomplete_is_positive_remaining_cost
#print axioms Prosa.Analysis.Facts.Behavior.Completion.incomplete_implies_positive_cost
#print axioms Prosa.Analysis.Facts.Behavior.Completion.scheduled_implies_positive_cost
#print axioms Prosa.Analysis.Facts.Behavior.Completion.service_lt_cost
#print axioms Prosa.Analysis.Facts.Behavior.Completion.completed_on_arrival_implies_zero_cost
#print axioms Prosa.Analysis.Facts.Behavior.Completion.serviced_implies_positive_remaining_cost
#print axioms Prosa.Analysis.Facts.Behavior.Completion.scheduled_implies_serviced
#print axioms Prosa.Analysis.Facts.Behavior.Completion.scheduled_implies_positive_remaining_cost
#print axioms Prosa.Analysis.Facts.Behavior.Completion.scheduled_implies_not_completed
#print axioms Prosa.Analysis.Facts.Behavior.Completion.not_scheduled_remains_incomplete
#print axioms Prosa.Analysis.Facts.Behavior.Completion.completed_implies_not_scheduled
#print axioms Prosa.Analysis.Facts.Behavior.Completion.not_pending_earlier_and_at_0
#print axioms Prosa.Analysis.Facts.Behavior.Completion.unit_service
#print axioms Prosa.Analysis.Facts.Behavior.Completion.service_at_most_cost
#print axioms Prosa.Analysis.Facts.Behavior.Completion.service_cost_invariant
#print axioms Prosa.Analysis.Facts.Behavior.Completion.cumulative_service_le_job_cost
#print axioms Prosa.Analysis.Facts.Behavior.Completion.job_doesnt_complete_before_remaining_cost
#print axioms Prosa.Analysis.Facts.Behavior.Completion.has_arrived_scheduled
#print axioms Prosa.Analysis.Facts.Behavior.Completion.scheduled_implies_pending
#print axioms Prosa.Analysis.Facts.Behavior.Completion.completed_implies_scheduled_before
#print axioms Prosa.Analysis.Facts.Behavior.Completion.job_pending_at_arrival
#print axioms Prosa.Analysis.Facts.Behavior.Completion.ready_implies_incomplete
#print axioms Prosa.Analysis.Facts.Behavior.Completion.completed_jobs_are_not_ready
#print axioms Prosa.Analysis.Facts.Behavior.Completion.valid_schedule_implies_completed_jobs_dont_execute
#print axioms Prosa.Analysis.Facts.Behavior.Completion.ideal_progress_completed_jobs
#print axioms Prosa.Analysis.Facts.Behavior.Completion.identical_prefix_completed_by
#print axioms Prosa.Analysis.Facts.Behavior.Completion.identical_prefix_pending
