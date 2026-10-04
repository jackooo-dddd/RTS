import Validation.fixtures.translation_order.ClassicUniJitterScheduleInterface
set_option pp.fieldNotation false

#check @Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule.UniprocessorScheduleWithJitter.pending
#check @Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule.UniprocessorScheduleWithJitter.backlogged
#check @Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule.UniprocessorScheduleWithJitter.jobs_execute_after_jitter
#check @Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule.UniprocessorScheduleWithJitter.jobs_with_jitter_must_arrive_to_execute
#check @Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule.UniprocessorScheduleWithJitter.jitter_has_passed_implies_arrived
#check @Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule.UniprocessorScheduleWithJitter.service_before_jitter_is_zero
#check @Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule.UniprocessorScheduleWithJitter.cumulative_service_before_jitter_is_zero
#check @Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule.UniprocessorScheduleWithJitter.ignore_service_before_jitter
#check @Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule.UniprocessorScheduleWithJitter.scheduled_implies_pending

#print axioms Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule.UniprocessorScheduleWithJitter.pending
#print axioms Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule.UniprocessorScheduleWithJitter.backlogged
#print axioms Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule.UniprocessorScheduleWithJitter.jobs_execute_after_jitter
#print axioms Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule.UniprocessorScheduleWithJitter.jobs_with_jitter_must_arrive_to_execute
#print axioms Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule.UniprocessorScheduleWithJitter.jitter_has_passed_implies_arrived
#print axioms Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule.UniprocessorScheduleWithJitter.service_before_jitter_is_zero
#print axioms Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule.UniprocessorScheduleWithJitter.cumulative_service_before_jitter_is_zero
#print axioms Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule.UniprocessorScheduleWithJitter.ignore_service_before_jitter
#print axioms Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule.UniprocessorScheduleWithJitter.scheduled_implies_pending
