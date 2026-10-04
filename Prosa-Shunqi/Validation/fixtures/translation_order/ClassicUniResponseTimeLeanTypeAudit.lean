import Validation.fixtures.translation_order.ClassicUniResponseTimeInterface
set_option pp.fieldNotation false

#check @Prosa.Classic.Model.Schedule.Uni.ResponseTime.ResponseTime.is_response_time_bound_of_job
#check @Prosa.Classic.Model.Schedule.Uni.ResponseTime.ResponseTime.is_response_time_bound_of_task
#check @Prosa.Classic.Model.Schedule.Uni.ResponseTime.ResponseTime.service_after_job_rt_zero
#check @Prosa.Classic.Model.Schedule.Uni.ResponseTime.ResponseTime.cumulative_service_after_job_rt_zero
#check @Prosa.Classic.Model.Schedule.Uni.ResponseTime.ResponseTime.service_after_task_rt_zero
#check @Prosa.Classic.Model.Schedule.Uni.ResponseTime.ResponseTime.cumulative_service_after_task_rt_zero

#print axioms Prosa.Classic.Model.Schedule.Uni.ResponseTime.ResponseTime.is_response_time_bound_of_job
#print axioms Prosa.Classic.Model.Schedule.Uni.ResponseTime.ResponseTime.is_response_time_bound_of_task
#print axioms Prosa.Classic.Model.Schedule.Uni.ResponseTime.ResponseTime.service_after_job_rt_zero
#print axioms Prosa.Classic.Model.Schedule.Uni.ResponseTime.ResponseTime.cumulative_service_after_job_rt_zero
#print axioms Prosa.Classic.Model.Schedule.Uni.ResponseTime.ResponseTime.service_after_task_rt_zero
#print axioms Prosa.Classic.Model.Schedule.Uni.ResponseTime.ResponseTime.cumulative_service_after_task_rt_zero
