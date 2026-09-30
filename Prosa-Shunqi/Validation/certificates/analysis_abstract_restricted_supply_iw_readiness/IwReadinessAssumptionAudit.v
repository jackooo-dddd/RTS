From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence WorkloadCorrespondence AbstractDefinitionsBaseAdapter ServiceBaseAdapter ServiceNatBoolOperations AbstractDefinitionsArrivalOperations AbstractDefinitionsClasses AbstractDefinitionsNatBoolOperations AbstractDefinitionsIntervalOperations AbstractDefinitionsOperations AbstractDefinitionsSums AbstractDefinitionsLogical ServiceIntervalOperations ServiceScheduleOperations AbstractDefinitionsPendingOperations AbstractDefinitionsTaskOperations AbstractDefinitionsBusyIntervalHelpers AbstractRtaHelpers JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence TaskPreemptionParametersCorrespondence IdealAbstractRtaHelpers ArrivalSequenceBaseAdapter ArrivalSequenceOperations TaskScheduleCorrespondence CurvesCorrespondence RequestBoundFunctionCorrespondence SequentialityCorrespondence ServiceOfJobsCorrespondence SupplyScheduleBaseAdapter SupplyScheduleFiniteOperations SupplyScheduleOperations SupplyBaseAdapter SupplyNatBoolOperations SupplyIntervalOperations SupplyCorrespondence IbfTaskHelpers IbfSupplyTaskCorrespondence IbfTaskFullHelpers ServiceInversionPredCorrespondence InterferenceCorrespondence AbstractDefinitionsBusyInterval PriorityBaseAdapter ReadinessInterferenceCorrespondence ReadinessAwareCorrespondence IwReadinessCorrespondence.
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

Goal Logic.True. idtac "AUDIT_BEGIN pending_hep_job_exists_inside_busy_interval_correspondence". exact Logic.I. Qed.
Print Assumptions pending_hep_job_exists_inside_busy_interval_correspondence.
Goal Logic.True. idtac "AUDIT_END pending_hep_job_exists_inside_busy_interval_correspondence". exact Logic.I. Qed.

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
