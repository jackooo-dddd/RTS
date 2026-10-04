import Validation.fixtures.translation_order.ClassicUniLimitedScheduleInterface
set_option pp.fieldNotation false

#check @Prosa.Classic.Model.Schedule.Uni.Limited.Schedule.job_lock_in_service_positive
#check @Prosa.Classic.Model.Schedule.Uni.Limited.Schedule.job_lock_in_service_le_job_cost
#check @Prosa.Classic.Model.Schedule.Uni.Limited.Schedule.job_nonpreemptive_after_lock_in_service
#check @Prosa.Classic.Model.Schedule.Uni.Limited.Schedule.proper_job_lock_in_service
#check @Prosa.Classic.Model.Schedule.Uni.Limited.Schedule.task_lock_in_service_le_task_cost
#check @Prosa.Classic.Model.Schedule.Uni.Limited.Schedule.task_lock_in_service_bounds_job_lock_in_service
#check @Prosa.Classic.Model.Schedule.Uni.Limited.Schedule.proper_task_lock_in_service
#check @Prosa.Classic.Model.Schedule.Uni.Limited.Schedule.job_nonpreemptive_after_lock_in_service_trivial
#check @Prosa.Classic.Model.Schedule.Uni.Limited.Schedule.property_last_segment_is_nonpreemptive_holds

#print axioms Prosa.Classic.Model.Schedule.Uni.Limited.Schedule.job_lock_in_service_positive
#print axioms Prosa.Classic.Model.Schedule.Uni.Limited.Schedule.job_lock_in_service_le_job_cost
#print axioms Prosa.Classic.Model.Schedule.Uni.Limited.Schedule.job_nonpreemptive_after_lock_in_service
#print axioms Prosa.Classic.Model.Schedule.Uni.Limited.Schedule.proper_job_lock_in_service
#print axioms Prosa.Classic.Model.Schedule.Uni.Limited.Schedule.task_lock_in_service_le_task_cost
#print axioms Prosa.Classic.Model.Schedule.Uni.Limited.Schedule.task_lock_in_service_bounds_job_lock_in_service
#print axioms Prosa.Classic.Model.Schedule.Uni.Limited.Schedule.proper_task_lock_in_service
#print axioms Prosa.Classic.Model.Schedule.Uni.Limited.Schedule.job_nonpreemptive_after_lock_in_service_trivial
#print axioms Prosa.Classic.Model.Schedule.Uni.Limited.Schedule.property_last_segment_is_nonpreemptive_holds
