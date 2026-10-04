import Validation.fixtures.translation_order.ClassicGlobalJitterScheduleInterface
set_option pp.fieldNotation false

#check @Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleWithJitter.actual_arrival
#check @Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleWithJitter.jitter_has_passed
#check @Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleWithJitter.actual_arrival_before
#check @Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleWithJitter.pending
#check @Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleWithJitter.backlogged
#check @Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleWithJitter.jobs_execute_after_jitter
#check @Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleWithJitter.scheduled_implies_pending
#check @Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleWithJitter.arrival_before_jitter
#check @Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleWithJitter.service_before_jitter_zero
#check @Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleWithJitter.cumulative_service_before_jitter_zero
#check @Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleOfSporadicTaskWithJitter.task_scheduled_on
#check @Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleOfSporadicTaskWithJitter.task_is_scheduled
#check @Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleOfSporadicTaskWithJitter.jobs_of_task_scheduled_between
#check @Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleOfSporadicTaskWithJitter.jobs_of_same_task_dont_execute_in_parallel
#check @Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleOfSporadicTaskWithJitter.cumulative_service_le_task_cost
#check @Prosa.Validation.ClassicGlobalJitterScheduleInterface.finRange_any
#check @Prosa.Validation.ClassicGlobalJitterScheduleInterface.bigCatFin_range'
#check @Prosa.Validation.ClassicGlobalJitterScheduleInterface.fin_sum_range'
#check @Prosa.Validation.ClassicGlobalJitterScheduleInterface.bigCat_range'
#check @Prosa.Validation.ClassicGlobalJitterScheduleInterface.count_filter_eq
#check @Prosa.Validation.ClassicGlobalJitterScheduleInterface.service_at_sum
#check @Prosa.Validation.ClassicGlobalJitterScheduleInterface.dedup_nil
#check @Prosa.Validation.ClassicGlobalJitterScheduleInterface.dedup_cons_mem
#check @Prosa.Validation.ClassicGlobalJitterScheduleInterface.dedup_cons_not_mem

#print axioms Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleWithJitter.actual_arrival
#print axioms Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleWithJitter.jitter_has_passed
#print axioms Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleWithJitter.actual_arrival_before
#print axioms Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleWithJitter.pending
#print axioms Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleWithJitter.backlogged
#print axioms Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleWithJitter.jobs_execute_after_jitter
#print axioms Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleWithJitter.scheduled_implies_pending
#print axioms Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleWithJitter.arrival_before_jitter
#print axioms Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleWithJitter.service_before_jitter_zero
#print axioms Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleWithJitter.cumulative_service_before_jitter_zero
#print axioms Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleOfSporadicTaskWithJitter.task_scheduled_on
#print axioms Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleOfSporadicTaskWithJitter.task_is_scheduled
#print axioms Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleOfSporadicTaskWithJitter.jobs_of_task_scheduled_between
#print axioms Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleOfSporadicTaskWithJitter.jobs_of_same_task_dont_execute_in_parallel
#print axioms Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleOfSporadicTaskWithJitter.cumulative_service_le_task_cost
#print axioms Prosa.Validation.ClassicGlobalJitterScheduleInterface.finRange_any
#print axioms Prosa.Validation.ClassicGlobalJitterScheduleInterface.bigCatFin_range'
#print axioms Prosa.Validation.ClassicGlobalJitterScheduleInterface.fin_sum_range'
#print axioms Prosa.Validation.ClassicGlobalJitterScheduleInterface.bigCat_range'
#print axioms Prosa.Validation.ClassicGlobalJitterScheduleInterface.count_filter_eq
#print axioms Prosa.Validation.ClassicGlobalJitterScheduleInterface.service_at_sum
#print axioms Prosa.Validation.ClassicGlobalJitterScheduleInterface.dedup_nil
#print axioms Prosa.Validation.ClassicGlobalJitterScheduleInterface.dedup_cons_mem
#print axioms Prosa.Validation.ClassicGlobalJitterScheduleInterface.dedup_cons_not_mem
