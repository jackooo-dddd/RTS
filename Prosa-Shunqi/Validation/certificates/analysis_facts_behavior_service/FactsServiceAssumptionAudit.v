From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations FsvcScheduledHelpers FactsServiceCorrespondence.

Goal Logic.True. idtac "AUDIT_BEGIN service_during_geq_correspondence". exact Logic.I. Qed.
Print Assumptions service_during_geq_correspondence.
Goal Logic.True. idtac "AUDIT_END service_during_geq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_during_ge_correspondence". exact Logic.I. Qed.
Print Assumptions service_during_ge_correspondence.
Goal Logic.True. idtac "AUDIT_END service_during_ge_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service0_correspondence". exact Logic.I. Qed.
Print Assumptions service0_correspondence.
Goal Logic.True. idtac "AUDIT_END service0_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_during_instant_correspondence". exact Logic.I. Qed.
Print Assumptions service_during_instant_correspondence.
Goal Logic.True. idtac "AUDIT_END service_during_instant_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_during_cat_correspondence". exact Logic.I. Qed.
Print Assumptions service_during_cat_correspondence.
Goal Logic.True. idtac "AUDIT_END service_during_cat_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_cat_correspondence". exact Logic.I. Qed.
Print Assumptions service_cat_correspondence.
Goal Logic.True. idtac "AUDIT_END service_cat_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_during_first_plus_later_correspondence". exact Logic.I. Qed.
Print Assumptions service_during_first_plus_later_correspondence.
Goal Logic.True. idtac "AUDIT_END service_during_first_plus_later_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_during_last_plus_before_correspondence". exact Logic.I. Qed.
Print Assumptions service_during_last_plus_before_correspondence.
Goal Logic.True. idtac "AUDIT_END service_during_last_plus_before_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_last_plus_before_correspondence". exact Logic.I. Qed.
Print Assumptions service_last_plus_before_correspondence.
Goal Logic.True. idtac "AUDIT_END service_last_plus_before_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_split_at_point_correspondence". exact Logic.I. Qed.
Print Assumptions service_split_at_point_correspondence.
Goal Logic.True. idtac "AUDIT_END service_split_at_point_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_at_most_one_correspondence". exact Logic.I. Qed.
Print Assumptions service_at_most_one_correspondence.
Goal Logic.True. idtac "AUDIT_END service_at_most_one_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_is_zero_or_one_correspondence". exact Logic.I. Qed.
Print Assumptions service_is_zero_or_one_correspondence.
Goal Logic.True. idtac "AUDIT_END service_is_zero_or_one_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cumulative_service_le_delta_correspondence". exact Logic.I. Qed.
Print Assumptions cumulative_service_le_delta_correspondence.
Goal Logic.True. idtac "AUDIT_END cumulative_service_le_delta_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cumulative_service_ge_delta_correspondence". exact Logic.I. Qed.
Print Assumptions cumulative_service_ge_delta_correspondence.
Goal Logic.True. idtac "AUDIT_END cumulative_service_ge_delta_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_during_is_unit_growth_function_correspondence". exact Logic.I. Qed.
Print Assumptions service_during_is_unit_growth_function_correspondence.
Goal Logic.True. idtac "AUDIT_END service_during_is_unit_growth_function_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_is_unit_growth_function_correspondence". exact Logic.I. Qed.
Print Assumptions service_is_unit_growth_function_correspondence.
Goal Logic.True. idtac "AUDIT_END service_is_unit_growth_function_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN exists_intermediate_service_during_correspondence". exact Logic.I. Qed.
Print Assumptions exists_intermediate_service_during_correspondence.
Goal Logic.True. idtac "AUDIT_END exists_intermediate_service_during_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN exists_intermediate_service_correspondence". exact Logic.I. Qed.
Print Assumptions exists_intermediate_service_correspondence.
Goal Logic.True. idtac "AUDIT_END exists_intermediate_service_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ideal_progress_inside_supplies_correspondence". exact Logic.I. Qed.
Print Assumptions ideal_progress_inside_supplies_correspondence.
Goal Logic.True. idtac "AUDIT_END ideal_progress_inside_supplies_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_monotonic_correspondence". exact Logic.I. Qed.
Print Assumptions service_monotonic_correspondence.
Goal Logic.True. idtac "AUDIT_END service_monotonic_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_in_implies_scheduled_in_correspondence". exact Logic.I. Qed.
Print Assumptions service_in_implies_scheduled_in_correspondence.
Goal Logic.True. idtac "AUDIT_END service_in_implies_scheduled_in_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN not_scheduled_implies_no_service_correspondence". exact Logic.I. Qed.
Print Assumptions not_scheduled_implies_no_service_correspondence.
Goal Logic.True. idtac "AUDIT_END not_scheduled_implies_no_service_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN not_scheduled_during_implies_zero_service_correspondence". exact Logic.I. Qed.
Print Assumptions not_scheduled_during_implies_zero_service_correspondence.
Goal Logic.True. idtac "AUDIT_END not_scheduled_during_implies_zero_service_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_at_implies_scheduled_at_correspondence". exact Logic.I. Qed.
Print Assumptions service_at_implies_scheduled_at_correspondence.
Goal Logic.True. idtac "AUDIT_END service_at_implies_scheduled_at_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_delta_implies_scheduled_correspondence". exact Logic.I. Qed.
Print Assumptions service_delta_implies_scheduled_correspondence.
Goal Logic.True. idtac "AUDIT_END service_delta_implies_scheduled_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_during_service_at_correspondence". exact Logic.I. Qed.
Print Assumptions service_during_service_at_correspondence.
Goal Logic.True. idtac "AUDIT_END service_during_service_at_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cumulative_service_implies_scheduled_correspondence". exact Logic.I. Qed.
Print Assumptions cumulative_service_implies_scheduled_correspondence.
Goal Logic.True. idtac "AUDIT_END cumulative_service_implies_scheduled_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN positive_service_implies_scheduled_before_correspondence". exact Logic.I. Qed.
Print Assumptions positive_service_implies_scheduled_before_correspondence.
Goal Logic.True. idtac "AUDIT_END positive_service_implies_scheduled_before_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_during_service_at_earliest_correspondence". exact Logic.I. Qed.
Print Assumptions service_during_service_at_earliest_correspondence.
Goal Logic.True. idtac "AUDIT_END service_during_service_at_earliest_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_during_scheduled_at_earliest_correspondence". exact Logic.I. Qed.
Print Assumptions service_during_scheduled_at_earliest_correspondence.
Goal Logic.True. idtac "AUDIT_END service_during_scheduled_at_earliest_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN no_service_not_scheduled_correspondence". exact Logic.I. Qed.
Print Assumptions no_service_not_scheduled_correspondence.
Goal Logic.True. idtac "AUDIT_END no_service_not_scheduled_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN no_service_during_implies_not_scheduled_correspondence". exact Logic.I. Qed.
Print Assumptions no_service_during_implies_not_scheduled_correspondence.
Goal Logic.True. idtac "AUDIT_END no_service_during_implies_not_scheduled_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN scheduled_implies_cumulative_service_correspondence". exact Logic.I. Qed.
Print Assumptions scheduled_implies_cumulative_service_correspondence.
Goal Logic.True. idtac "AUDIT_END scheduled_implies_cumulative_service_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN scheduled_implies_nonzero_service_correspondence". exact Logic.I. Qed.
Print Assumptions scheduled_implies_nonzero_service_correspondence.
Goal Logic.True. idtac "AUDIT_END scheduled_implies_nonzero_service_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN unit_service_at1_correspondence". exact Logic.I. Qed.
Print Assumptions unit_service_at1_correspondence.
Goal Logic.True. idtac "AUDIT_END unit_service_at1_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN not_scheduled_before_arrival_correspondence". exact Logic.I. Qed.
Print Assumptions not_scheduled_before_arrival_correspondence.
Goal Logic.True. idtac "AUDIT_END not_scheduled_before_arrival_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN positive_service_implies_scheduled_since_arrival_correspondence". exact Logic.I. Qed.
Print Assumptions positive_service_implies_scheduled_since_arrival_correspondence.
Goal Logic.True. idtac "AUDIT_END positive_service_implies_scheduled_since_arrival_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_before_job_arrival_zero_correspondence". exact Logic.I. Qed.
Print Assumptions service_before_job_arrival_zero_correspondence.
Goal Logic.True. idtac "AUDIT_END service_before_job_arrival_zero_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cumulative_service_before_job_arrival_zero_correspondence". exact Logic.I. Qed.
Print Assumptions cumulative_service_before_job_arrival_zero_correspondence.
Goal Logic.True. idtac "AUDIT_END cumulative_service_before_job_arrival_zero_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ignore_service_before_arrival_correspondence". exact Logic.I. Qed.
Print Assumptions ignore_service_before_arrival_correspondence.
Goal Logic.True. idtac "AUDIT_END ignore_service_before_arrival_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN no_service_before_arrival_correspondence". exact Logic.I. Qed.
Print Assumptions no_service_before_arrival_correspondence.
Goal Logic.True. idtac "AUDIT_END no_service_before_arrival_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN constant_service_implies_no_service_during_correspondence". exact Logic.I. Qed.
Print Assumptions constant_service_implies_no_service_during_correspondence.
Goal Logic.True. idtac "AUDIT_END constant_service_implies_no_service_during_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN constant_service_implies_not_scheduled_correspondence". exact Logic.I. Qed.
Print Assumptions constant_service_implies_not_scheduled_correspondence.
Goal Logic.True. idtac "AUDIT_END constant_service_implies_not_scheduled_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN same_service_implies_serviced_at_earlier_times_correspondence". exact Logic.I. Qed.
Print Assumptions same_service_implies_serviced_at_earlier_times_correspondence.
Goal Logic.True. idtac "AUDIT_END same_service_implies_serviced_at_earlier_times_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN same_service_implies_scheduled_at_earlier_times_correspondence". exact Logic.I. Qed.
Print Assumptions same_service_implies_scheduled_at_earlier_times_correspondence.
Goal Logic.True. idtac "AUDIT_END same_service_implies_scheduled_at_earlier_times_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN receives_service_and_served_at_consistent_correspondence". exact Logic.I. Qed.
Print Assumptions receives_service_and_served_at_consistent_correspondence.
Goal Logic.True. idtac "AUDIT_END receives_service_and_served_at_consistent_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN served_at_and_receives_service_consistent_correspondence". exact Logic.I. Qed.
Print Assumptions served_at_and_receives_service_consistent_correspondence.
Goal Logic.True. idtac "AUDIT_END served_at_and_receives_service_consistent_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN no_service_received_when_idle_correspondence". exact Logic.I. Qed.
Print Assumptions no_service_received_when_idle_correspondence.
Goal Logic.True. idtac "AUDIT_END no_service_received_when_idle_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN receives_service_implies_has_supply_correspondence". exact Logic.I. Qed.
Print Assumptions receives_service_implies_has_supply_correspondence.
Goal Logic.True. idtac "AUDIT_END receives_service_implies_has_supply_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN no_blackout_when_service_received_correspondence". exact Logic.I. Qed.
Print Assumptions no_blackout_when_service_received_correspondence.
Goal Logic.True. idtac "AUDIT_END no_blackout_when_service_received_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN no_service_during_blackout_correspondence". exact Logic.I. Qed.
Print Assumptions no_service_during_blackout_correspondence.
Goal Logic.True. idtac "AUDIT_END no_service_during_blackout_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN only_one_job_receives_service_at_uni_correspondence". exact Logic.I. Qed.
Print Assumptions only_one_job_receives_service_at_uni_correspondence.
Goal Logic.True. idtac "AUDIT_END only_one_job_receives_service_at_uni_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN incremental_service_during_correspondence". exact Logic.I. Qed.
Print Assumptions incremental_service_during_correspondence.
Goal Logic.True. idtac "AUDIT_END incremental_service_during_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN kth_scheduling_time_correspondence". exact Logic.I. Qed.
Print Assumptions kth_scheduling_time_correspondence.
Goal Logic.True. idtac "AUDIT_END kth_scheduling_time_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN same_service_during_correspondence". exact Logic.I. Qed.
Print Assumptions same_service_during_correspondence.
Goal Logic.True. idtac "AUDIT_END same_service_during_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN equal_prefix_implies_same_service_during_correspondence". exact Logic.I. Qed.
Print Assumptions equal_prefix_implies_same_service_during_correspondence.
Goal Logic.True. idtac "AUDIT_END equal_prefix_implies_same_service_during_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN identical_prefix_service_correspondence". exact Logic.I. Qed.
Print Assumptions identical_prefix_service_correspondence.
Goal Logic.True. idtac "AUDIT_END identical_prefix_service_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsv_supply_in_related". exact Logic.I. Qed.
Print Assumptions fsv_supply_in_related.
Goal Logic.True. idtac "AUDIT_END fsv_supply_in_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsv_unit_service_related". exact Logic.I. Qed.
Print Assumptions fsv_unit_service_related.
Goal Logic.True. idtac "AUDIT_END fsv_unit_service_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsv_fully_consuming_related". exact Logic.I. Qed.
Print Assumptions fsv_fully_consuming_related.
Goal Logic.True. idtac "AUDIT_END fsv_fully_consuming_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsv_unit_growth_related". exact Logic.I. Qed.
Print Assumptions fsv_unit_growth_related.
Goal Logic.True. idtac "AUDIT_END fsv_unit_growth_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsv_exists_nat". exact Logic.I. Qed.
Print Assumptions fsv_exists_nat.
Goal Logic.True. idtac "AUDIT_END fsv_exists_nat". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsv_exists_ord_related". exact Logic.I. Qed.
Print Assumptions fsv_exists_ord_related.
Goal Logic.True. idtac "AUDIT_END fsv_exists_ord_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsv_state_eq_correspondence". exact Logic.I. Qed.
Print Assumptions fsv_state_eq_correspondence.
Goal Logic.True. idtac "AUDIT_END fsv_state_eq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsv_any_nat_canonical". exact Logic.I. Qed.
Print Assumptions fsv_any_nat_canonical.
Goal Logic.True. idtac "AUDIT_END fsv_any_nat_canonical". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsv_exists_ord_has". exact Logic.I. Qed.
Print Assumptions fsv_exists_ord_has.
Goal Logic.True. idtac "AUDIT_END fsv_exists_ord_has". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsv_bool_eq_correspondence". exact Logic.I. Qed.
Print Assumptions fsv_bool_eq_correspondence.
Goal Logic.True. idtac "AUDIT_END fsv_bool_eq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fs_forall_schedule". exact Logic.I. Qed.
Print Assumptions fs_forall_schedule.
Goal Logic.True. idtac "AUDIT_END fs_forall_schedule". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fs_forall_state". exact Logic.I. Qed.
Print Assumptions fs_forall_state.
Goal Logic.True. idtac "AUDIT_END fs_forall_state". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsv_service_during_related". exact Logic.I. Qed.
Print Assumptions fsv_service_during_related.
Goal Logic.True. idtac "AUDIT_END fsv_service_during_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsv_is_blackout_related". exact Logic.I. Qed.
Print Assumptions fsv_is_blackout_related.
Goal Logic.True. idtac "AUDIT_END fsv_is_blackout_related". exact Logic.I. Qed.
