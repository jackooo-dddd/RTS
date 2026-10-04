import Validation.fixtures.translation_order.ClassicResponseTimeInterface
set_option pp.fieldNotation false

#check @Prosa.Classic.Model.Schedule.Global.ResponseTime.ResponseTime.is_response_time_bound_of_task
#check @Prosa.Classic.Model.Schedule.Global.ResponseTime.ResponseTime.service_after_job_rt_zero
#check @Prosa.Classic.Model.Schedule.Global.ResponseTime.ResponseTime.cumulative_service_after_job_rt_zero
#check @Prosa.Classic.Model.Schedule.Global.ResponseTime.ResponseTime.service_after_task_rt_zero
#check @Prosa.Classic.Model.Schedule.Global.ResponseTime.ResponseTime.cumulative_service_after_task_rt_zero
#check @Prosa.Validation.ClassicResponseTimeInterface.fin_sum_range'
#check @Prosa.Validation.ClassicResponseTimeInterface.service_at_sum

#print axioms Prosa.Classic.Model.Schedule.Global.ResponseTime.ResponseTime.is_response_time_bound_of_task
#print axioms Prosa.Classic.Model.Schedule.Global.ResponseTime.ResponseTime.service_after_job_rt_zero
#print axioms Prosa.Classic.Model.Schedule.Global.ResponseTime.ResponseTime.cumulative_service_after_job_rt_zero
#print axioms Prosa.Classic.Model.Schedule.Global.ResponseTime.ResponseTime.service_after_task_rt_zero
#print axioms Prosa.Classic.Model.Schedule.Global.ResponseTime.ResponseTime.cumulative_service_after_task_rt_zero
#print axioms Prosa.Validation.ClassicResponseTimeInterface.fin_sum_range'
#print axioms Prosa.Validation.ClassicResponseTimeInterface.service_at_sum
