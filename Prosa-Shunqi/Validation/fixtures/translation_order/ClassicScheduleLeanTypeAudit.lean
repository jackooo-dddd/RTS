import Validation.fixtures.translation_order.ClassicScheduleInterface
set_option pp.fieldNotation false

#check @Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.processor
#check @Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.schedule
#check @Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.scheduled_on
#check @Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.scheduled
#check @Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.is_idle
#check @Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.service_at
#check @Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.service
#check @Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.service_during
#check @Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.completed
#check @Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.pending
#check @Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.backlogged
#check @Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.carried_in
#check @Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.carried_out
#check @Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.jobs_scheduled_at
#check @Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.jobs_scheduled_between
#check @Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.sequential_jobs
#check @Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.jobs_must_arrive_to_execute
#check @Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.completed_jobs_dont_execute
#check @Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.jobs_come_from_arrival_sequence
#check @Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.not_scheduled_no_service
#check @Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.cumulative_service_implies_service
#check @Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.service_implies_cumulative_service
#check @Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.service_at_most_one
#check @Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.cumulative_service_le_delta
#check @Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.completion_monotonic
#check @Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.completed_implies_not_scheduled
#check @Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.cumulative_service_le_job_cost
#check @Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.service_before_job_arrival_zero
#check @Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.cumulative_service_before_job_arrival_zero
#check @Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.service_before_arrival_eq_service_during
#check @Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.scheduled_implies_pending
#check @Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.mem_scheduled_jobs_eq_scheduled
#check @Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.scheduled_jobs_uniq
#check @Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.num_scheduled_jobs_le_num_cpus
#check @Prosa.Classic.Model.Schedule.Global.Basic.Schedule.ScheduleOfSporadicTask.task_scheduled_on
#check @Prosa.Classic.Model.Schedule.Global.Basic.Schedule.ScheduleOfSporadicTask.task_is_scheduled
#check @Prosa.Classic.Model.Schedule.Global.Basic.Schedule.ScheduleOfSporadicTask.jobs_of_task_scheduled_between
#check @Prosa.Classic.Model.Schedule.Global.Basic.Schedule.ScheduleOfSporadicTask.jobs_of_same_task_dont_execute_in_parallel
#check @Prosa.Classic.Model.Schedule.Global.Basic.Schedule.ScheduleOfSporadicTask.cumulative_service_le_task_cost
#check @Prosa.Validation.ClassicScheduleInterface.finRange_any
#check @Prosa.Validation.ClassicScheduleInterface.bigCatFin_range'
#check @Prosa.Validation.ClassicScheduleInterface.fin_sum_range'
#check @Prosa.Validation.ClassicScheduleInterface.bigCat_range'
#check @Prosa.Validation.ClassicScheduleInterface.count_filter_eq
#check @Prosa.Validation.ClassicScheduleInterface.service_at_sum
#check @Prosa.Validation.ClassicScheduleInterface.dedup_nil
#check @Prosa.Validation.ClassicScheduleInterface.dedup_cons_mem
#check @Prosa.Validation.ClassicScheduleInterface.dedup_cons_not_mem

#print axioms Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.processor
#print axioms Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.schedule
#print axioms Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.scheduled_on
#print axioms Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.scheduled
#print axioms Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.is_idle
#print axioms Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.service_at
#print axioms Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.service
#print axioms Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.service_during
#print axioms Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.completed
#print axioms Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.pending
#print axioms Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.backlogged
#print axioms Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.carried_in
#print axioms Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.carried_out
#print axioms Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.jobs_scheduled_at
#print axioms Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.jobs_scheduled_between
#print axioms Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.sequential_jobs
#print axioms Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.jobs_must_arrive_to_execute
#print axioms Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.completed_jobs_dont_execute
#print axioms Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.jobs_come_from_arrival_sequence
#print axioms Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.not_scheduled_no_service
#print axioms Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.cumulative_service_implies_service
#print axioms Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.service_implies_cumulative_service
#print axioms Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.service_at_most_one
#print axioms Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.cumulative_service_le_delta
#print axioms Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.completion_monotonic
#print axioms Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.completed_implies_not_scheduled
#print axioms Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.cumulative_service_le_job_cost
#print axioms Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.service_before_job_arrival_zero
#print axioms Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.cumulative_service_before_job_arrival_zero
#print axioms Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.service_before_arrival_eq_service_during
#print axioms Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.scheduled_implies_pending
#print axioms Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.mem_scheduled_jobs_eq_scheduled
#print axioms Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.scheduled_jobs_uniq
#print axioms Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule.num_scheduled_jobs_le_num_cpus
#print axioms Prosa.Classic.Model.Schedule.Global.Basic.Schedule.ScheduleOfSporadicTask.task_scheduled_on
#print axioms Prosa.Classic.Model.Schedule.Global.Basic.Schedule.ScheduleOfSporadicTask.task_is_scheduled
#print axioms Prosa.Classic.Model.Schedule.Global.Basic.Schedule.ScheduleOfSporadicTask.jobs_of_task_scheduled_between
#print axioms Prosa.Classic.Model.Schedule.Global.Basic.Schedule.ScheduleOfSporadicTask.jobs_of_same_task_dont_execute_in_parallel
#print axioms Prosa.Classic.Model.Schedule.Global.Basic.Schedule.ScheduleOfSporadicTask.cumulative_service_le_task_cost
#print axioms Prosa.Validation.ClassicScheduleInterface.finRange_any
#print axioms Prosa.Validation.ClassicScheduleInterface.bigCatFin_range'
#print axioms Prosa.Validation.ClassicScheduleInterface.fin_sum_range'
#print axioms Prosa.Validation.ClassicScheduleInterface.bigCat_range'
#print axioms Prosa.Validation.ClassicScheduleInterface.count_filter_eq
#print axioms Prosa.Validation.ClassicScheduleInterface.service_at_sum
#print axioms Prosa.Validation.ClassicScheduleInterface.dedup_nil
#print axioms Prosa.Validation.ClassicScheduleInterface.dedup_cons_mem
#print axioms Prosa.Validation.ClassicScheduleInterface.dedup_cons_not_mem
