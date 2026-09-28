From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence WorkloadCorrespondence AbstractDefinitionsBaseAdapter ServiceBaseAdapter ServiceNatBoolOperations AbstractDefinitionsArrivalOperations AbstractDefinitionsClasses AbstractDefinitionsNatBoolOperations AbstractDefinitionsIntervalOperations AbstractDefinitionsOperations AbstractDefinitionsSums AbstractDefinitionsLogical ServiceIntervalOperations ServiceScheduleOperations AbstractDefinitionsPendingOperations AbstractDefinitionsTaskOperations AbstractDefinitionsBusyIntervalHelpers AbstractRtaHelpers JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence TaskPreemptionParametersCorrespondence IdealAbstractRtaHelpers ArrivalSequenceBaseAdapter ArrivalSequenceOperations TaskScheduleCorrespondence CurvesCorrespondence RequestBoundFunctionCorrespondence SequentialityCorrespondence ServiceOfJobsCorrespondence SupplyScheduleBaseAdapter SupplyScheduleFiniteOperations SupplyScheduleOperations SupplyBaseAdapter SupplyNatBoolOperations SupplyIntervalOperations SupplyCorrespondence IbfTaskHelpers IbfSupplyTaskCorrespondence IbfTaskFullHelpers ServiceInversionPredCorrespondence InterferenceCorrespondence RsIwInstantiationCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN cumulative_interference_split_correspondence". exact Logic.I. Qed.
Print Assumptions cumulative_interference_split_correspondence.
Goal Logic.True. idtac "AUDIT_END cumulative_interference_split_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cumulative_interfering_workload_split_correspondence". exact Logic.I. Qed.
Print Assumptions cumulative_interfering_workload_split_correspondence.
Goal Logic.True. idtac "AUDIT_END cumulative_interfering_workload_split_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cumulative_task_interference_split_correspondence". exact Logic.I. Qed.
Print Assumptions cumulative_task_interference_split_correspondence.
Goal Logic.True. idtac "AUDIT_END cumulative_task_interference_split_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cumulative_intra_interference_split_correspondence". exact Logic.I. Qed.
Print Assumptions cumulative_intra_interference_split_correspondence.
Goal Logic.True. idtac "AUDIT_END cumulative_intra_interference_split_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cumulative_iw_hep_eq_workload_of_ohep_correspondence". exact Logic.I. Qed.
Print Assumptions cumulative_iw_hep_eq_workload_of_ohep_correspondence.
Goal Logic.True. idtac "AUDIT_END cumulative_iw_hep_eq_workload_of_ohep_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN quiet_time_cl_implies_quiet_time_ab_correspondence". exact Logic.I. Qed.
Print Assumptions quiet_time_cl_implies_quiet_time_ab_correspondence.
Goal Logic.True. idtac "AUDIT_END quiet_time_cl_implies_quiet_time_ab_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN quiet_time_ab_implies_quiet_time_cl_correspondence". exact Logic.I. Qed.
Print Assumptions quiet_time_ab_implies_quiet_time_cl_correspondence.
Goal Logic.True. idtac "AUDIT_END quiet_time_ab_implies_quiet_time_cl_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN instantiated_quiet_time_equivalent_quiet_time_correspondence". exact Logic.I. Qed.
Print Assumptions instantiated_quiet_time_equivalent_quiet_time_correspondence.
Goal Logic.True. idtac "AUDIT_END instantiated_quiet_time_equivalent_quiet_time_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN instantiated_busy_interval_prefix_equivalent_busy_interval_prefix_correspondence". exact Logic.I. Qed.
Print Assumptions instantiated_busy_interval_prefix_equivalent_busy_interval_prefix_correspondence.
Goal Logic.True. idtac "AUDIT_END instantiated_busy_interval_prefix_equivalent_busy_interval_prefix_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN instantiated_busy_interval_equivalent_busy_interval_correspondence". exact Logic.I. Qed.
Print Assumptions instantiated_busy_interval_equivalent_busy_interval_correspondence.
Goal Logic.True. idtac "AUDIT_END instantiated_busy_interval_equivalent_busy_interval_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN abstract_busy_interval_classic_quiet_time_correspondence". exact Logic.I. Qed.
Print Assumptions abstract_busy_interval_classic_quiet_time_correspondence.
Goal Logic.True. idtac "AUDIT_END abstract_busy_interval_classic_quiet_time_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN abstract_busy_interval_classic_busy_interval_prefix_correspondence". exact Logic.I. Qed.
Print Assumptions abstract_busy_interval_classic_busy_interval_prefix_correspondence.
Goal Logic.True. idtac "AUDIT_END abstract_busy_interval_classic_busy_interval_prefix_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN not_interference_implies_scheduled_correspondence". exact Logic.I. Qed.
Print Assumptions not_interference_implies_scheduled_correspondence.
Goal Logic.True. idtac "AUDIT_END not_interference_implies_scheduled_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN scheduled_implies_no_interference_correspondence". exact Logic.I. Qed.
Print Assumptions scheduled_implies_no_interference_correspondence.
Goal Logic.True. idtac "AUDIT_END scheduled_implies_no_interference_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN instantiated_i_and_w_are_coherent_with_schedule_correspondence". exact Logic.I. Qed.
Print Assumptions instantiated_i_and_w_are_coherent_with_schedule_correspondence.
Goal Logic.True. idtac "AUDIT_END instantiated_i_and_w_are_coherent_with_schedule_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN instantiated_interference_and_workload_consistent_with_sequential_tasks_correspondence". exact Logic.I. Qed.
Print Assumptions instantiated_interference_and_workload_consistent_with_sequential_tasks_correspondence.
Goal Logic.True. idtac "AUDIT_END instantiated_interference_and_workload_consistent_with_sequential_tasks_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN instantiated_i_and_w_no_speculative_execution_correspondence". exact Logic.I. Qed.
Print Assumptions instantiated_i_and_w_no_speculative_execution_correspondence.
Goal Logic.True. idtac "AUDIT_END instantiated_i_and_w_no_speculative_execution_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rsi_and_true_right". exact Logic.I. Qed.
Print Assumptions rsi_and_true_right.
Goal Logic.True. idtac "AUDIT_END rsi_and_true_right". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rsi_and_absorb_target". exact Logic.I. Qed.
Print Assumptions rsi_and_absorb_target.
Goal Logic.True. idtac "AUDIT_END rsi_and_absorb_target". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rsi_and_absorb_source". exact Logic.I. Qed.
Print Assumptions rsi_and_absorb_source.
Goal Logic.True. idtac "AUDIT_END rsi_and_absorb_source". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rsi_bool_true_of_rel". exact Logic.I. Qed.
Print Assumptions rsi_bool_true_of_rel.
Goal Logic.True. idtac "AUDIT_END rsi_bool_true_of_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rsi_exists_identity". exact Logic.I. Qed.
Print Assumptions rsi_exists_identity.
Goal Logic.True. idtac "AUDIT_END rsi_exists_identity". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rsi_hs_sup". exact Logic.I. Qed.
Print Assumptions rsi_hs_sup.
Goal Logic.True. idtac "AUDIT_END rsi_hs_sup". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rsi_hs_jsvc". exact Logic.I. Qed.
Print Assumptions rsi_hs_jsvc.
Goal Logic.True. idtac "AUDIT_END rsi_hs_jsvc". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rsi_forall_sched". exact Logic.I. Qed.
Print Assumptions rsi_forall_sched.
Goal Logic.True. idtac "AUDIT_END rsi_forall_sched". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rsi_forall_arr". exact Logic.I. Qed.
Print Assumptions rsi_forall_arr.
Goal Logic.True. idtac "AUDIT_END rsi_forall_arr". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rsi_forall_state". exact Logic.I. Qed.
Print Assumptions rsi_forall_state.
Goal Logic.True. idtac "AUDIT_END rsi_forall_state". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rsi_forall_jlfp". exact Logic.I. Qed.
Print Assumptions rsi_forall_jlfp.
Goal Logic.True. idtac "AUDIT_END rsi_forall_jlfp". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rsi_reflexive_rel". exact Logic.I. Qed.
Print Assumptions rsi_reflexive_rel.
Goal Logic.True. idtac "AUDIT_END rsi_reflexive_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rsi_jlfp_to_jldp_rel". exact Logic.I. Qed.
Print Assumptions rsi_jlfp_to_jldp_rel.
Goal Logic.True. idtac "AUDIT_END rsi_jlfp_to_jldp_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rsi_policy_respects_sequential_rel". exact Logic.I. Qed.
Print Assumptions rsi_policy_respects_sequential_rel.
Goal Logic.True. idtac "AUDIT_END rsi_policy_respects_sequential_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rsi_unit_supply_rel". exact Logic.I. Qed.
Print Assumptions rsi_unit_supply_rel.
Goal Logic.True. idtac "AUDIT_END rsi_unit_supply_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rsi_fully_consuming_rel". exact Logic.I. Qed.
Print Assumptions rsi_fully_consuming_rel.
Goal Logic.True. idtac "AUDIT_END rsi_fully_consuming_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rsi_must_arrive_rel". exact Logic.I. Qed.
Print Assumptions rsi_must_arrive_rel.
Goal Logic.True. idtac "AUDIT_END rsi_must_arrive_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rsi_completed_dont_execute_rel". exact Logic.I. Qed.
Print Assumptions rsi_completed_dont_execute_rel.
Goal Logic.True. idtac "AUDIT_END rsi_completed_dont_execute_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rsi_receives_service_at_related". exact Logic.I. Qed.
Print Assumptions rsi_receives_service_at_related.
Goal Logic.True. idtac "AUDIT_END rsi_receives_service_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rsi_service_inversion_related". exact Logic.I. Qed.
Print Assumptions rsi_service_inversion_related.
Goal Logic.True. idtac "AUDIT_END rsi_service_inversion_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rsi_interference_rel". exact Logic.I. Qed.
Print Assumptions rsi_interference_rel.
Goal Logic.True. idtac "AUDIT_END rsi_interference_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rsi_workload_rel". exact Logic.I. Qed.
Print Assumptions rsi_workload_rel.
Goal Logic.True. idtac "AUDIT_END rsi_workload_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rsi_interference_related". exact Logic.I. Qed.
Print Assumptions rsi_interference_related.
Goal Logic.True. idtac "AUDIT_END rsi_interference_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rsi_quiet_time_related". exact Logic.I. Qed.
Print Assumptions rsi_quiet_time_related.
Goal Logic.True. idtac "AUDIT_END rsi_quiet_time_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rsi_busy_interval_prefix_related". exact Logic.I. Qed.
Print Assumptions rsi_busy_interval_prefix_related.
Goal Logic.True. idtac "AUDIT_END rsi_busy_interval_prefix_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rsi_busy_interval_related". exact Logic.I. Qed.
Print Assumptions rsi_busy_interval_related.
Goal Logic.True. idtac "AUDIT_END rsi_busy_interval_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rsi_ab_quiet_time_related". exact Logic.I. Qed.
Print Assumptions rsi_ab_quiet_time_related.
Goal Logic.True. idtac "AUDIT_END rsi_ab_quiet_time_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rsi_ab_busy_interval_prefix_related". exact Logic.I. Qed.
Print Assumptions rsi_ab_busy_interval_prefix_related.
Goal Logic.True. idtac "AUDIT_END rsi_ab_busy_interval_prefix_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rsi_ab_busy_interval_related". exact Logic.I. Qed.
Print Assumptions rsi_ab_busy_interval_related.
Goal Logic.True. idtac "AUDIT_END rsi_ab_busy_interval_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rsi_jr_to_target_rel". exact Logic.I. Qed.
Print Assumptions rsi_jr_to_target_rel.
Goal Logic.True. idtac "AUDIT_END rsi_jr_to_target_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rsi_jr_to_source_rel". exact Logic.I. Qed.
Print Assumptions rsi_jr_to_source_rel.
Goal Logic.True. idtac "AUDIT_END rsi_jr_to_source_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rsi_forall_jr". exact Logic.I. Qed.
Print Assumptions rsi_forall_jr.
Goal Logic.True. idtac "AUDIT_END rsi_forall_jr". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rsi_valid_schedule_rel". exact Logic.I. Qed.
Print Assumptions rsi_valid_schedule_rel.
Goal Logic.True. idtac "AUDIT_END rsi_valid_schedule_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rsi_backlogged_related". exact Logic.I. Qed.
Print Assumptions rsi_backlogged_related.
Goal Logic.True. idtac "AUDIT_END rsi_backlogged_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rsi_work_conserving_related". exact Logic.I. Qed.
Print Assumptions rsi_work_conserving_related.
Goal Logic.True. idtac "AUDIT_END rsi_work_conserving_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rsi_work_bearing_related". exact Logic.I. Qed.
Print Assumptions rsi_work_bearing_related.
Goal Logic.True. idtac "AUDIT_END rsi_work_bearing_related". exact Logic.I. Qed.
