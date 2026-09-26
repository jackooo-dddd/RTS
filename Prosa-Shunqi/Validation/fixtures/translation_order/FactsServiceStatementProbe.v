Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.FactsServiceSemanticSource.
Import FactsServiceSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
Require Import prosa.util.unit_growth prosa.model.schedule.scheduled prosa.analysis.definitions.service.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.service_during_geq". Abort.
Print statement_service_during_geq.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.service_during_geq". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.service_during_ge". Abort.
Print statement_service_during_ge.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.service_during_ge". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.service0". Abort.
Print statement_service0.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.service0". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.service_during_instant". Abort.
Print statement_service_during_instant.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.service_during_instant". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.service_during_cat". Abort.
Print statement_service_during_cat.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.service_during_cat". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.service_cat". Abort.
Print statement_service_cat.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.service_cat". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.service_during_first_plus_later". Abort.
Print statement_service_during_first_plus_later.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.service_during_first_plus_later". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.service_during_last_plus_before". Abort.
Print statement_service_during_last_plus_before.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.service_during_last_plus_before". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.service_last_plus_before". Abort.
Print statement_service_last_plus_before.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.service_last_plus_before". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.service_split_at_point". Abort.
Print statement_service_split_at_point.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.service_split_at_point". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.service_at_most_one". Abort.
Print statement_service_at_most_one.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.service_at_most_one". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.service_is_zero_or_one". Abort.
Print statement_service_is_zero_or_one.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.service_is_zero_or_one". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.cumulative_service_le_delta". Abort.
Print statement_cumulative_service_le_delta.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.cumulative_service_le_delta". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.cumulative_service_ge_delta". Abort.
Print statement_cumulative_service_ge_delta.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.cumulative_service_ge_delta". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.service_during_is_unit_growth_function". Abort.
Print statement_service_during_is_unit_growth_function.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.service_during_is_unit_growth_function". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.service_is_unit_growth_function". Abort.
Print statement_service_is_unit_growth_function.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.service_is_unit_growth_function". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.exists_intermediate_service_during". Abort.
Print statement_exists_intermediate_service_during.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.exists_intermediate_service_during". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.exists_intermediate_service". Abort.
Print statement_exists_intermediate_service.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.exists_intermediate_service". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.ideal_progress_inside_supplies". Abort.
Print statement_ideal_progress_inside_supplies.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.ideal_progress_inside_supplies". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.service_monotonic". Abort.
Print statement_service_monotonic.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.service_monotonic". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.service_in_implies_scheduled_in". Abort.
Print statement_service_in_implies_scheduled_in.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.service_in_implies_scheduled_in". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.not_scheduled_implies_no_service". Abort.
Print statement_not_scheduled_implies_no_service.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.not_scheduled_implies_no_service". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.not_scheduled_during_implies_zero_service". Abort.
Print statement_not_scheduled_during_implies_zero_service.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.not_scheduled_during_implies_zero_service". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.service_at_implies_scheduled_at". Abort.
Print statement_service_at_implies_scheduled_at.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.service_at_implies_scheduled_at". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.service_delta_implies_scheduled". Abort.
Print statement_service_delta_implies_scheduled.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.service_delta_implies_scheduled". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.service_during_service_at". Abort.
Print statement_service_during_service_at.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.service_during_service_at". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.cumulative_service_implies_scheduled". Abort.
Print statement_cumulative_service_implies_scheduled.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.cumulative_service_implies_scheduled". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.positive_service_implies_scheduled_before". Abort.
Print statement_positive_service_implies_scheduled_before.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.positive_service_implies_scheduled_before". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.service_during_service_at_earliest". Abort.
Print statement_service_during_service_at_earliest.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.service_during_service_at_earliest". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.service_during_scheduled_at_earliest". Abort.
Print statement_service_during_scheduled_at_earliest.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.service_during_scheduled_at_earliest". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.no_service_not_scheduled". Abort.
Print statement_no_service_not_scheduled.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.no_service_not_scheduled". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.no_service_during_implies_not_scheduled". Abort.
Print statement_no_service_during_implies_not_scheduled.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.no_service_during_implies_not_scheduled". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.scheduled_implies_cumulative_service". Abort.
Print statement_scheduled_implies_cumulative_service.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.scheduled_implies_cumulative_service". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.scheduled_implies_nonzero_service". Abort.
Print statement_scheduled_implies_nonzero_service.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.scheduled_implies_nonzero_service". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.unit_service_at1". Abort.
Print statement_unit_service_at1.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.unit_service_at1". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.not_scheduled_before_arrival". Abort.
Print statement_not_scheduled_before_arrival.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.not_scheduled_before_arrival". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.positive_service_implies_scheduled_since_arrival". Abort.
Print statement_positive_service_implies_scheduled_since_arrival.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.positive_service_implies_scheduled_since_arrival". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.service_before_job_arrival_zero". Abort.
Print statement_service_before_job_arrival_zero.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.service_before_job_arrival_zero". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.cumulative_service_before_job_arrival_zero". Abort.
Print statement_cumulative_service_before_job_arrival_zero.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.cumulative_service_before_job_arrival_zero". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.ignore_service_before_arrival". Abort.
Print statement_ignore_service_before_arrival.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.ignore_service_before_arrival". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.no_service_before_arrival". Abort.
Print statement_no_service_before_arrival.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.no_service_before_arrival". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.constant_service_implies_no_service_during". Abort.
Print statement_constant_service_implies_no_service_during.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.constant_service_implies_no_service_during". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.constant_service_implies_not_scheduled". Abort.
Print statement_constant_service_implies_not_scheduled.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.constant_service_implies_not_scheduled". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.same_service_implies_serviced_at_earlier_times". Abort.
Print statement_same_service_implies_serviced_at_earlier_times.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.same_service_implies_serviced_at_earlier_times". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.same_service_implies_scheduled_at_earlier_times". Abort.
Print statement_same_service_implies_scheduled_at_earlier_times.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.same_service_implies_scheduled_at_earlier_times". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.receives_service_and_served_at_consistent". Abort.
Print statement_receives_service_and_served_at_consistent.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.receives_service_and_served_at_consistent". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.served_at_and_receives_service_consistent". Abort.
Print statement_served_at_and_receives_service_consistent.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.served_at_and_receives_service_consistent". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.no_service_received_when_idle". Abort.
Print statement_no_service_received_when_idle.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.no_service_received_when_idle". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.receives_service_implies_has_supply". Abort.
Print statement_receives_service_implies_has_supply.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.receives_service_implies_has_supply". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.no_blackout_when_service_received". Abort.
Print statement_no_blackout_when_service_received.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.no_blackout_when_service_received". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.no_service_during_blackout". Abort.
Print statement_no_service_during_blackout.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.no_service_during_blackout". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.only_one_job_receives_service_at_uni". Abort.
Print statement_only_one_job_receives_service_at_uni.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.only_one_job_receives_service_at_uni". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.incremental_service_during". Abort.
Print statement_incremental_service_during.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.incremental_service_during". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.kth_scheduling_time". Abort.
Print statement_kth_scheduling_time.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.kth_scheduling_time". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.same_service_during". Abort.
Print statement_same_service_during.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.same_service_during". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.equal_prefix_implies_same_service_during". Abort.
Print statement_equal_prefix_implies_same_service_during.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.equal_prefix_implies_same_service_during". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.identical_prefix_service". Abort.
Print statement_identical_prefix_service.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.identical_prefix_service". Abort.
