import Validation.fixtures.translation_order.ClassicUniLimitedBusyIntervalInterface
set_option pp.fieldNotation false

#check @Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.quiet_time
#check @Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.busy_interval_prefix
#check @Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.busy_interval
#check @Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.is_priority_inversion
#check @Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.cumulative_priority_inversion
#check @Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.priority_inversion_of_job_is_bounded_by
#check @Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.priority_inversion_is_bounded_by
#check @Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.quiet_time_dec
#check @Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.quiet_time_P
#check @Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.job_completes_within_busy_interval
#check @Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.not_quiet_implies_exists_pending_job
#check @Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.idle_time_implies_quiet_time_at_the_next_time_instant
#check @Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.pending_hp_job_exists
#check @Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.not_quiet_implies_not_idle
#check @Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.hep_jobs_receive_no_service_before_quiet_time
#check @Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.no_idle_time_within_non_quiet_time_interval
#check @Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.exists_busy_interval_prefix
#check @Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.busy_interval_has_uninterrupted_service
#check @Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.busy_interval_too_much_workload
#check @Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.busy_interval_workload_larger_than_interval
#check @Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.busy_interval_is_bounded
#check @Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.exists_busy_interval
#check @Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.busy_interval_bounds_response_time
#check @Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.no_carry_in
#check @Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.no_carry_in_implies_quiet_time
#check @Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.idle_instant_implies_no_carry_in_at_t
#check @Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.idle_instant_implies_no_carry_in_at_t_pl_1
#check @Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.no_carry_in_at_the_beginning
#check @Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.total_service_is_bounded_by_Δ
#check @Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.low_total_service_implies_existence_of_time_with_no_carry_in
#check @Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.completion_of_all_jobs_implies_no_carry_in
#check @Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.processor_is_not_too_busy
#check @Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.exists_busy_interval_from_total_workload_bound
#check @Prosa.Validation.ClassicUniLimitedBusyIntervalInterface.bigCat_range'
#check @Prosa.Validation.ClassicUniLimitedBusyIntervalInterface.production_sumSeq_nil
#check @Prosa.Validation.ClassicUniLimitedBusyIntervalInterface.production_sumSeq_cons
#check @Prosa.Validation.ClassicUniLimitedBusyIntervalInterface.production_sumFiltered_nil
#check @Prosa.Validation.ClassicUniLimitedBusyIntervalInterface.production_sumFiltered_cons_true
#check @Prosa.Validation.ClassicUniLimitedBusyIntervalInterface.production_sumFiltered_cons_false

#print axioms Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.quiet_time
#print axioms Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.busy_interval_prefix
#print axioms Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.busy_interval
#print axioms Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.is_priority_inversion
#print axioms Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.cumulative_priority_inversion
#print axioms Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.priority_inversion_of_job_is_bounded_by
#print axioms Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.priority_inversion_is_bounded_by
#print axioms Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.quiet_time_dec
#print axioms Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.quiet_time_P
#print axioms Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.job_completes_within_busy_interval
#print axioms Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.not_quiet_implies_exists_pending_job
#print axioms Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.idle_time_implies_quiet_time_at_the_next_time_instant
#print axioms Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.pending_hp_job_exists
#print axioms Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.not_quiet_implies_not_idle
#print axioms Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.hep_jobs_receive_no_service_before_quiet_time
#print axioms Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.no_idle_time_within_non_quiet_time_interval
#print axioms Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.exists_busy_interval_prefix
#print axioms Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.busy_interval_has_uninterrupted_service
#print axioms Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.busy_interval_too_much_workload
#print axioms Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.busy_interval_workload_larger_than_interval
#print axioms Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.busy_interval_is_bounded
#print axioms Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.exists_busy_interval
#print axioms Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.busy_interval_bounds_response_time
#print axioms Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.no_carry_in
#print axioms Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.no_carry_in_implies_quiet_time
#print axioms Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.idle_instant_implies_no_carry_in_at_t
#print axioms Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.idle_instant_implies_no_carry_in_at_t_pl_1
#print axioms Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.no_carry_in_at_the_beginning
#print axioms Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.total_service_is_bounded_by_Δ
#print axioms Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.low_total_service_implies_existence_of_time_with_no_carry_in
#print axioms Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.completion_of_all_jobs_implies_no_carry_in
#print axioms Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.processor_is_not_too_busy
#print axioms Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.exists_busy_interval_from_total_workload_bound
#print axioms Prosa.Validation.ClassicUniLimitedBusyIntervalInterface.bigCat_range'
#print axioms Prosa.Validation.ClassicUniLimitedBusyIntervalInterface.production_sumSeq_nil
#print axioms Prosa.Validation.ClassicUniLimitedBusyIntervalInterface.production_sumSeq_cons
#print axioms Prosa.Validation.ClassicUniLimitedBusyIntervalInterface.production_sumFiltered_nil
#print axioms Prosa.Validation.ClassicUniLimitedBusyIntervalInterface.production_sumFiltered_cons_true
#print axioms Prosa.Validation.ClassicUniLimitedBusyIntervalInterface.production_sumFiltered_cons_false
