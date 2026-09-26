import Prosa.Analysis.Facts.Behavior.Service
set_option pp.fieldNotation false

#check @Prosa.Analysis.Facts.Behavior.Service.service_during_geq
#check @Prosa.Analysis.Facts.Behavior.Service.service_during_ge
#check @Prosa.Analysis.Facts.Behavior.Service.service0
#check @Prosa.Analysis.Facts.Behavior.Service.service_during_instant
#check @Prosa.Analysis.Facts.Behavior.Service.service_during_cat
#check @Prosa.Analysis.Facts.Behavior.Service.service_cat
#check @Prosa.Analysis.Facts.Behavior.Service.service_during_first_plus_later
#check @Prosa.Analysis.Facts.Behavior.Service.service_during_last_plus_before
#check @Prosa.Analysis.Facts.Behavior.Service.service_last_plus_before
#check @Prosa.Analysis.Facts.Behavior.Service.service_split_at_point
#check @Prosa.Analysis.Facts.Behavior.Service.service_at_most_one
#check @Prosa.Analysis.Facts.Behavior.Service.service_is_zero_or_one
#check @Prosa.Analysis.Facts.Behavior.Service.cumulative_service_le_delta
#check @Prosa.Analysis.Facts.Behavior.Service.cumulative_service_ge_delta
#check @Prosa.Analysis.Facts.Behavior.Service.service_during_is_unit_growth_function
#check @Prosa.Analysis.Facts.Behavior.Service.service_is_unit_growth_function
#check @Prosa.Analysis.Facts.Behavior.Service.exists_intermediate_service_during
#check @Prosa.Analysis.Facts.Behavior.Service.exists_intermediate_service
#check @Prosa.Analysis.Facts.Behavior.Service.ideal_progress_inside_supplies
#check @Prosa.Analysis.Facts.Behavior.Service.service_monotonic
#check @Prosa.Analysis.Facts.Behavior.Service.service_in_implies_scheduled_in
#check @Prosa.Analysis.Facts.Behavior.Service.not_scheduled_implies_no_service
#check @Prosa.Analysis.Facts.Behavior.Service.not_scheduled_during_implies_zero_service
#check @Prosa.Analysis.Facts.Behavior.Service.service_at_implies_scheduled_at
#check @Prosa.Analysis.Facts.Behavior.Service.service_delta_implies_scheduled
#check @Prosa.Analysis.Facts.Behavior.Service.service_during_service_at
#check @Prosa.Analysis.Facts.Behavior.Service.cumulative_service_implies_scheduled
#check @Prosa.Analysis.Facts.Behavior.Service.positive_service_implies_scheduled_before
#check @Prosa.Analysis.Facts.Behavior.Service.service_during_service_at_earliest
#check @Prosa.Analysis.Facts.Behavior.Service.service_during_scheduled_at_earliest
#check @Prosa.Analysis.Facts.Behavior.Service.no_service_not_scheduled
#check @Prosa.Analysis.Facts.Behavior.Service.no_service_during_implies_not_scheduled
#check @Prosa.Analysis.Facts.Behavior.Service.scheduled_implies_cumulative_service
#check @Prosa.Analysis.Facts.Behavior.Service.scheduled_implies_nonzero_service
#check @Prosa.Analysis.Facts.Behavior.Service.unit_service_at1
#check @Prosa.Analysis.Facts.Behavior.Service.not_scheduled_before_arrival
#check @Prosa.Analysis.Facts.Behavior.Service.positive_service_implies_scheduled_since_arrival
#check @Prosa.Analysis.Facts.Behavior.Service.service_before_job_arrival_zero
#check @Prosa.Analysis.Facts.Behavior.Service.cumulative_service_before_job_arrival_zero
#check @Prosa.Analysis.Facts.Behavior.Service.ignore_service_before_arrival
#check @Prosa.Analysis.Facts.Behavior.Service.no_service_before_arrival
#check @Prosa.Analysis.Facts.Behavior.Service.constant_service_implies_no_service_during
#check @Prosa.Analysis.Facts.Behavior.Service.constant_service_implies_not_scheduled
#check @Prosa.Analysis.Facts.Behavior.Service.same_service_implies_serviced_at_earlier_times
#check @Prosa.Analysis.Facts.Behavior.Service.same_service_implies_scheduled_at_earlier_times
#check @Prosa.Analysis.Facts.Behavior.Service.receives_service_and_served_at_consistent
#check @Prosa.Analysis.Facts.Behavior.Service.served_at_and_receives_service_consistent
#check @Prosa.Analysis.Facts.Behavior.Service.no_service_received_when_idle
#check @Prosa.Analysis.Facts.Behavior.Service.receives_service_implies_has_supply
#check @Prosa.Analysis.Facts.Behavior.Service.no_blackout_when_service_received
#check @Prosa.Analysis.Facts.Behavior.Service.no_service_during_blackout
#check @Prosa.Analysis.Facts.Behavior.Service.only_one_job_receives_service_at_uni
#check @Prosa.Analysis.Facts.Behavior.Service.incremental_service_during
#check @Prosa.Analysis.Facts.Behavior.Service.kth_scheduling_time
#check @Prosa.Analysis.Facts.Behavior.Service.same_service_during
#check @Prosa.Analysis.Facts.Behavior.Service.equal_prefix_implies_same_service_during
#check @Prosa.Analysis.Facts.Behavior.Service.identical_prefix_service

#print axioms Prosa.Analysis.Facts.Behavior.Service.service_during_geq
#print axioms Prosa.Analysis.Facts.Behavior.Service.service_during_ge
#print axioms Prosa.Analysis.Facts.Behavior.Service.service0
#print axioms Prosa.Analysis.Facts.Behavior.Service.service_during_instant
#print axioms Prosa.Analysis.Facts.Behavior.Service.service_during_cat
#print axioms Prosa.Analysis.Facts.Behavior.Service.service_cat
#print axioms Prosa.Analysis.Facts.Behavior.Service.service_during_first_plus_later
#print axioms Prosa.Analysis.Facts.Behavior.Service.service_during_last_plus_before
#print axioms Prosa.Analysis.Facts.Behavior.Service.service_last_plus_before
#print axioms Prosa.Analysis.Facts.Behavior.Service.service_split_at_point
#print axioms Prosa.Analysis.Facts.Behavior.Service.service_at_most_one
#print axioms Prosa.Analysis.Facts.Behavior.Service.service_is_zero_or_one
#print axioms Prosa.Analysis.Facts.Behavior.Service.cumulative_service_le_delta
#print axioms Prosa.Analysis.Facts.Behavior.Service.cumulative_service_ge_delta
#print axioms Prosa.Analysis.Facts.Behavior.Service.service_during_is_unit_growth_function
#print axioms Prosa.Analysis.Facts.Behavior.Service.service_is_unit_growth_function
#print axioms Prosa.Analysis.Facts.Behavior.Service.exists_intermediate_service_during
#print axioms Prosa.Analysis.Facts.Behavior.Service.exists_intermediate_service
#print axioms Prosa.Analysis.Facts.Behavior.Service.ideal_progress_inside_supplies
#print axioms Prosa.Analysis.Facts.Behavior.Service.service_monotonic
#print axioms Prosa.Analysis.Facts.Behavior.Service.service_in_implies_scheduled_in
#print axioms Prosa.Analysis.Facts.Behavior.Service.not_scheduled_implies_no_service
#print axioms Prosa.Analysis.Facts.Behavior.Service.not_scheduled_during_implies_zero_service
#print axioms Prosa.Analysis.Facts.Behavior.Service.service_at_implies_scheduled_at
#print axioms Prosa.Analysis.Facts.Behavior.Service.service_delta_implies_scheduled
#print axioms Prosa.Analysis.Facts.Behavior.Service.service_during_service_at
#print axioms Prosa.Analysis.Facts.Behavior.Service.cumulative_service_implies_scheduled
#print axioms Prosa.Analysis.Facts.Behavior.Service.positive_service_implies_scheduled_before
#print axioms Prosa.Analysis.Facts.Behavior.Service.service_during_service_at_earliest
#print axioms Prosa.Analysis.Facts.Behavior.Service.service_during_scheduled_at_earliest
#print axioms Prosa.Analysis.Facts.Behavior.Service.no_service_not_scheduled
#print axioms Prosa.Analysis.Facts.Behavior.Service.no_service_during_implies_not_scheduled
#print axioms Prosa.Analysis.Facts.Behavior.Service.scheduled_implies_cumulative_service
#print axioms Prosa.Analysis.Facts.Behavior.Service.scheduled_implies_nonzero_service
#print axioms Prosa.Analysis.Facts.Behavior.Service.unit_service_at1
#print axioms Prosa.Analysis.Facts.Behavior.Service.not_scheduled_before_arrival
#print axioms Prosa.Analysis.Facts.Behavior.Service.positive_service_implies_scheduled_since_arrival
#print axioms Prosa.Analysis.Facts.Behavior.Service.service_before_job_arrival_zero
#print axioms Prosa.Analysis.Facts.Behavior.Service.cumulative_service_before_job_arrival_zero
#print axioms Prosa.Analysis.Facts.Behavior.Service.ignore_service_before_arrival
#print axioms Prosa.Analysis.Facts.Behavior.Service.no_service_before_arrival
#print axioms Prosa.Analysis.Facts.Behavior.Service.constant_service_implies_no_service_during
#print axioms Prosa.Analysis.Facts.Behavior.Service.constant_service_implies_not_scheduled
#print axioms Prosa.Analysis.Facts.Behavior.Service.same_service_implies_serviced_at_earlier_times
#print axioms Prosa.Analysis.Facts.Behavior.Service.same_service_implies_scheduled_at_earlier_times
#print axioms Prosa.Analysis.Facts.Behavior.Service.receives_service_and_served_at_consistent
#print axioms Prosa.Analysis.Facts.Behavior.Service.served_at_and_receives_service_consistent
#print axioms Prosa.Analysis.Facts.Behavior.Service.no_service_received_when_idle
#print axioms Prosa.Analysis.Facts.Behavior.Service.receives_service_implies_has_supply
#print axioms Prosa.Analysis.Facts.Behavior.Service.no_blackout_when_service_received
#print axioms Prosa.Analysis.Facts.Behavior.Service.no_service_during_blackout
#print axioms Prosa.Analysis.Facts.Behavior.Service.only_one_job_receives_service_at_uni
#print axioms Prosa.Analysis.Facts.Behavior.Service.incremental_service_during
#print axioms Prosa.Analysis.Facts.Behavior.Service.kth_scheduling_time
#print axioms Prosa.Analysis.Facts.Behavior.Service.same_service_during
#print axioms Prosa.Analysis.Facts.Behavior.Service.equal_prefix_implies_same_service_during
#print axioms Prosa.Analysis.Facts.Behavior.Service.identical_prefix_service
