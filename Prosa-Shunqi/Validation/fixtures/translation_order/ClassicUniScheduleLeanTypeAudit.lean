import Validation.fixtures.translation_order.ClassicUniScheduleInterface
set_option pp.fieldNotation false

#check @Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.schedule
#check @Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.scheduled_at
#check @Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.service_at
#check @Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.service_during
#check @Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.service
#check @Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.completed_by
#check @Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.pending
#check @Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.pending_earlier_and_at
#check @Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.backlogged
#check @Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.is_idle
#check @Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.total_service_during
#check @Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.total_service
#check @Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.sequential_jobs
#check @Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.scheduler_executes_job_with_earliest_arrival
#check @Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.jobs_come_from_arrival_sequence
#check @Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.jobs_must_arrive_to_execute
#check @Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.completed_jobs_dont_execute
#check @Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.remaining_cost
#check @Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.service_at_most_one
#check @Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.cumulative_service_le_delta
#check @Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.scheduled_implies_positive_remaining_cost
#check @Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.completion_monotonic
#check @Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.completed_implies_not_scheduled
#check @Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.scheduled_implies_not_completed
#check @Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.cumulative_service_le_job_cost
#check @Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.job_doesnt_complete_before_remaining_cost
#check @Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.completed_implies_scheduled_before
#check @Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.service_before_job_arrival_zero
#check @Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.cumulative_service_before_job_arrival_zero
#check @Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.ignore_service_before_arrival
#check @Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.scheduled_implies_pending
#check @Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.job_pending_at_arrival
#check @Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.only_one_job_scheduled
#check @Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.service_is_a_step_function
#check @Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.exists_intermediate_service
#check @Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.scheduled_at_earlier_time
#check @Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.cumulative_service_implies_scheduled
#check @Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.same_service_implies_scheduled_at_earlier_times
#check @Prosa.Validation.ClassicUniScheduleInterface.finRange_map_shift
#check @Prosa.Validation.ClassicUniScheduleInterface.finRange_map_val
#check @Prosa.Validation.ClassicUniScheduleInterface.finRange_any

#print axioms Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.schedule
#print axioms Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.scheduled_at
#print axioms Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.service_at
#print axioms Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.service_during
#print axioms Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.service
#print axioms Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.completed_by
#print axioms Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.pending
#print axioms Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.pending_earlier_and_at
#print axioms Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.backlogged
#print axioms Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.is_idle
#print axioms Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.total_service_during
#print axioms Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.total_service
#print axioms Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.sequential_jobs
#print axioms Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.scheduler_executes_job_with_earliest_arrival
#print axioms Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.jobs_come_from_arrival_sequence
#print axioms Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.jobs_must_arrive_to_execute
#print axioms Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.completed_jobs_dont_execute
#print axioms Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.remaining_cost
#print axioms Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.service_at_most_one
#print axioms Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.cumulative_service_le_delta
#print axioms Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.scheduled_implies_positive_remaining_cost
#print axioms Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.completion_monotonic
#print axioms Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.completed_implies_not_scheduled
#print axioms Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.scheduled_implies_not_completed
#print axioms Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.cumulative_service_le_job_cost
#print axioms Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.job_doesnt_complete_before_remaining_cost
#print axioms Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.completed_implies_scheduled_before
#print axioms Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.service_before_job_arrival_zero
#print axioms Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.cumulative_service_before_job_arrival_zero
#print axioms Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.ignore_service_before_arrival
#print axioms Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.scheduled_implies_pending
#print axioms Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.job_pending_at_arrival
#print axioms Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.only_one_job_scheduled
#print axioms Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.service_is_a_step_function
#print axioms Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.exists_intermediate_service
#print axioms Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.scheduled_at_earlier_time
#print axioms Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.cumulative_service_implies_scheduled
#print axioms Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule.same_service_implies_scheduled_at_earlier_times
#print axioms Prosa.Validation.ClassicUniScheduleInterface.finRange_map_shift
#print axioms Prosa.Validation.ClassicUniScheduleInterface.finRange_map_val
#print axioms Prosa.Validation.ClassicUniScheduleInterface.finRange_any
