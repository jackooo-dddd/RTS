From FoundationCertificates Require Import
  IdlArrivalsSeqBaseAdapter IdlArrivalsSeqOperations IdlArrivalsSeqCorrespondence IdlArrivalsCorrespondence IdlWorkloadCorrespondence IdlAbstractDefinitionsBaseAdapter IdlServiceBaseAdapter IdlServiceNatBoolOperations IdlAbstractDefinitionsArrivalOperations IdlAbstractDefinitionsClasses IdlAbstractDefinitionsNatBoolOperations IdlAbstractDefinitionsIntervalOperations IdlAbstractDefinitionsOperations IdlAbstractDefinitionsSums IdlAbstractDefinitionsLogical IdlServiceIntervalOperations IdlServiceScheduleOperations IdlAbstractDefinitionsPendingOperations IdlAbstractDefinitionsTaskOperations IdlAbstractDefinitionsBusyIntervalHelpers IdlAbstractRtaHelpers IdlJitterSvcBaseAdapter IdlJitterSvcNatBoolOperations IdlJitterSvcIntervalOperations IdlJitterSvcScheduleOperations IdlJitterSvcJobOperations IdlPreemptionParameterCorrespondence IdlTaskPreemptionParametersCorrespondence IdlIdealAbstractRtaHelpers IdlArrivalSequenceBaseAdapter IdlArrivalSequenceOperations IdlTaskScheduleCorrespondence IdlCurvesCorrespondence IdlRequestBoundFunctionCorrespondence IdlSequentialityCorrespondence IdlServiceOfJobsCorrespondence IdlSupplyScheduleBaseAdapter IdlSupplyScheduleFiniteOperations IdlSupplyScheduleOperations IdlSupplyBaseAdapter IdlSupplyNatBoolOperations IdlSupplyIntervalOperations IdlSupplyCorrespondence IdlIbfTaskHelpers IdlIbfSupplyTaskCorrespondence IdlIbfTaskFullHelpers IdlServiceInversionPredCorrespondence IdlInterferenceCorrespondence IdlPriorityInversionCorrespondence IdlStateRel IdealIwInstantiationCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN no_interference_when_idle_correspondence". exact Logic.I. Qed.
Print Assumptions no_interference_when_idle_correspondence.
Goal Logic.True. idtac "AUDIT_END no_interference_when_idle_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN no_task_interference_when_idle_correspondence". exact Logic.I. Qed.
Print Assumptions no_task_interference_when_idle_correspondence.
Goal Logic.True. idtac "AUDIT_END no_task_interference_when_idle_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN task_interference_eq_false_correspondence". exact Logic.I. Qed.
Print Assumptions task_interference_eq_false_correspondence.
Goal Logic.True. idtac "AUDIT_END task_interference_eq_false_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sched_athep_implies_task_interference_correspondence". exact Logic.I. Qed.
Print Assumptions sched_athep_implies_task_interference_correspondence.
Goal Logic.True. idtac "AUDIT_END sched_athep_implies_task_interference_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cumulative_interference_split_correspondence". exact Logic.I. Qed.
Print Assumptions cumulative_interference_split_correspondence.
Goal Logic.True. idtac "AUDIT_END cumulative_interference_split_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cumulative_interfering_workload_split_correspondence". exact Logic.I. Qed.
Print Assumptions cumulative_interfering_workload_split_correspondence.
Goal Logic.True. idtac "AUDIT_END cumulative_interfering_workload_split_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cumulative_task_interference_split_correspondence". exact Logic.I. Qed.
Print Assumptions cumulative_task_interference_split_correspondence.
Goal Logic.True. idtac "AUDIT_END cumulative_task_interference_split_correspondence". exact Logic.I. Qed.

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

Goal Logic.True. idtac "AUDIT_BEGIN instantiated_busy_intervals_are_bounded_correspondence". exact Logic.I. Qed.
Print Assumptions instantiated_busy_intervals_are_bounded_correspondence.
Goal Logic.True. idtac "AUDIT_END instantiated_busy_intervals_are_bounded_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN idl_idle_related". exact Logic.I. Qed.
Print Assumptions idl_idle_related.
Goal Logic.True. idtac "AUDIT_END idl_idle_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN idl_all_jobs_from_taskset_rel". exact Logic.I. Qed.
Print Assumptions idl_all_jobs_from_taskset_rel.
Goal Logic.True. idtac "AUDIT_END idl_all_jobs_from_taskset_rel". exact Logic.I. Qed.
