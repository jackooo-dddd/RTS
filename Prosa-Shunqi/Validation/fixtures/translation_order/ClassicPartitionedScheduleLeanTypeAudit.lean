import Validation.fixtures.translation_order.ClassicPartitionedScheduleInterface
set_option pp.fieldNotation false

#check @Prosa.Classic.Model.Schedule.Partitioned.Schedule.Partitioned.never_migrates
#check @Prosa.Classic.Model.Schedule.Partitioned.Schedule.Partitioned.job_local_to_processor
#check @Prosa.Classic.Model.Schedule.Partitioned.Schedule.Partitioned.task_local_to_processor
#check @Prosa.Classic.Model.Schedule.Partitioned.Schedule.Partitioned.partitioned_schedule
#check @Prosa.Classic.Model.Schedule.Partitioned.Schedule.Partitioned.local_jobs_dont_migrate
#check @Prosa.Validation.ClassicPartitionedScheduleInterface.finRange_any
#check @Prosa.Validation.ClassicPartitionedScheduleInterface.bigCatFin_range'
#check @Prosa.Validation.ClassicPartitionedScheduleInterface.fin_sum_range'
#check @Prosa.Validation.ClassicPartitionedScheduleInterface.bigCat_range'
#check @Prosa.Validation.ClassicPartitionedScheduleInterface.count_filter_eq
#check @Prosa.Validation.ClassicPartitionedScheduleInterface.service_at_sum
#check @Prosa.Validation.ClassicPartitionedScheduleInterface.dedup_nil
#check @Prosa.Validation.ClassicPartitionedScheduleInterface.dedup_cons_mem
#check @Prosa.Validation.ClassicPartitionedScheduleInterface.dedup_cons_not_mem

#print axioms Prosa.Classic.Model.Schedule.Partitioned.Schedule.Partitioned.never_migrates
#print axioms Prosa.Classic.Model.Schedule.Partitioned.Schedule.Partitioned.job_local_to_processor
#print axioms Prosa.Classic.Model.Schedule.Partitioned.Schedule.Partitioned.task_local_to_processor
#print axioms Prosa.Classic.Model.Schedule.Partitioned.Schedule.Partitioned.partitioned_schedule
#print axioms Prosa.Classic.Model.Schedule.Partitioned.Schedule.Partitioned.local_jobs_dont_migrate
#print axioms Prosa.Validation.ClassicPartitionedScheduleInterface.finRange_any
#print axioms Prosa.Validation.ClassicPartitionedScheduleInterface.bigCatFin_range'
#print axioms Prosa.Validation.ClassicPartitionedScheduleInterface.fin_sum_range'
#print axioms Prosa.Validation.ClassicPartitionedScheduleInterface.bigCat_range'
#print axioms Prosa.Validation.ClassicPartitionedScheduleInterface.count_filter_eq
#print axioms Prosa.Validation.ClassicPartitionedScheduleInterface.service_at_sum
#print axioms Prosa.Validation.ClassicPartitionedScheduleInterface.dedup_nil
#print axioms Prosa.Validation.ClassicPartitionedScheduleInterface.dedup_cons_mem
#print axioms Prosa.Validation.ClassicPartitionedScheduleInterface.dedup_cons_not_mem
