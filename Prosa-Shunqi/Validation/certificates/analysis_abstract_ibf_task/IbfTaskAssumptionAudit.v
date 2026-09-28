From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence WorkloadCorrespondence AbstractDefinitionsBaseAdapter ServiceBaseAdapter ServiceNatBoolOperations AbstractDefinitionsArrivalOperations AbstractDefinitionsClasses AbstractDefinitionsNatBoolOperations AbstractDefinitionsIntervalOperations AbstractDefinitionsOperations AbstractDefinitionsSums AbstractDefinitionsLogical ServiceIntervalOperations ServiceScheduleOperations AbstractDefinitionsPendingOperations AbstractDefinitionsTaskOperations AbstractDefinitionsBusyIntervalHelpers AbstractRtaHelpers JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence TaskPreemptionParametersCorrespondence IdealAbstractRtaHelpers ArrivalSequenceBaseAdapter ArrivalSequenceOperations TaskScheduleCorrespondence CurvesCorrespondence RequestBoundFunctionCorrespondence SequentialityCorrespondence ServiceOfJobsCorrespondence IbfTaskCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN nonself_correspondence". exact Logic.I. Qed.
Print Assumptions nonself_correspondence.
Goal Logic.True. idtac "AUDIT_END nonself_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN task_interference_correspondence". exact Logic.I. Qed.
Print Assumptions task_interference_correspondence.
Goal Logic.True. idtac "AUDIT_END task_interference_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cumul_task_interference_correspondence". exact Logic.I. Qed.
Print Assumptions cumul_task_interference_correspondence.
Goal Logic.True. idtac "AUDIT_END cumul_task_interference_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN task_interference_is_bounded_by_correspondence". exact Logic.I. Qed.
Print Assumptions task_interference_is_bounded_by_correspondence.
Goal Logic.True. idtac "AUDIT_END task_interference_is_bounded_by_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN interference_and_workload_consistent_with_sequential_tasks_correspondence". exact Logic.I. Qed.
Print Assumptions interference_and_workload_consistent_with_sequential_tasks_correspondence.
Goal Logic.True. idtac "AUDIT_END interference_and_workload_consistent_with_sequential_tasks_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN completed_before_beginning_of_busy_interval_correspondence". exact Logic.I. Qed.
Print Assumptions completed_before_beginning_of_busy_interval_correspondence.
Goal Logic.True. idtac "AUDIT_END completed_before_beginning_of_busy_interval_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arrives_after_beginning_of_busy_interval_correspondence". exact Logic.I. Qed.
Print Assumptions arrives_after_beginning_of_busy_interval_correspondence.
Goal Logic.True. idtac "AUDIT_END arrives_after_beginning_of_busy_interval_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN interference_plus_sched_le_serv_of_task_plus_task_interference_idle_correspondence". exact Logic.I. Qed.
Print Assumptions interference_plus_sched_le_serv_of_task_plus_task_interference_idle_correspondence.
Goal Logic.True. idtac "AUDIT_END interference_plus_sched_le_serv_of_task_plus_task_interference_idle_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN interference_plus_sched_le_serv_of_task_plus_task_interference_task_correspondence". exact Logic.I. Qed.
Print Assumptions interference_plus_sched_le_serv_of_task_plus_task_interference_task_correspondence.
Goal Logic.True. idtac "AUDIT_END interference_plus_sched_le_serv_of_task_plus_task_interference_task_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN interference_plus_sched_le_serv_of_task_plus_task_interference_job_correspondence". exact Logic.I. Qed.
Print Assumptions interference_plus_sched_le_serv_of_task_plus_task_interference_job_correspondence.
Goal Logic.True. idtac "AUDIT_END interference_plus_sched_le_serv_of_task_plus_task_interference_job_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN interference_and_service_eq_1_correspondence". exact Logic.I. Qed.
Print Assumptions interference_and_service_eq_1_correspondence.
Goal Logic.True. idtac "AUDIT_END interference_and_service_eq_1_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN interference_plus_sched_le_serv_of_task_plus_task_interference_j_correspondence". exact Logic.I. Qed.
Print Assumptions interference_plus_sched_le_serv_of_task_plus_task_interference_j_correspondence.
Goal Logic.True. idtac "AUDIT_END interference_plus_sched_le_serv_of_task_plus_task_interference_j_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN interference_plus_sched_le_serv_of_task_plus_task_interference_correspondence". exact Logic.I. Qed.
Print Assumptions interference_plus_sched_le_serv_of_task_plus_task_interference_correspondence.
Goal Logic.True. idtac "AUDIT_END interference_plus_sched_le_serv_of_task_plus_task_interference_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cumul_interference_plus_sched_le_serv_of_task_plus_cumul_task_interference_correspondence". exact Logic.I. Qed.
Print Assumptions cumul_interference_plus_sched_le_serv_of_task_plus_cumul_task_interference_correspondence.
Goal Logic.True. idtac "AUDIT_END cumul_interference_plus_sched_le_serv_of_task_plus_cumul_task_interference_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN serv_of_task_le_workload_of_task_plus_correspondence". exact Logic.I. Qed.
Print Assumptions serv_of_task_le_workload_of_task_plus_correspondence.
Goal Logic.True. idtac "AUDIT_END serv_of_task_le_workload_of_task_plus_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cumulative_job_interference_le_task_interference_bound_correspondence". exact Logic.I. Qed.
Print Assumptions cumulative_job_interference_le_task_interference_bound_correspondence.
Goal Logic.True. idtac "AUDIT_END cumulative_job_interference_le_task_interference_bound_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cumulative_job_interference_bound_correspondence". exact Logic.I. Qed.
Print Assumptions cumulative_job_interference_bound_correspondence.
Goal Logic.True. idtac "AUDIT_END cumulative_job_interference_bound_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN task_IBF_implies_job_IBF_correspondence". exact Logic.I. Qed.
Print Assumptions task_IBF_implies_job_IBF_correspondence.
Goal Logic.True. idtac "AUDIT_END task_IBF_implies_job_IBF_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ibt_nonself_pred". exact Logic.I. Qed.
Print Assumptions ibt_nonself_pred.
Goal Logic.True. idtac "AUDIT_END ibt_nonself_pred". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ibt_arr_ad". exact Logic.I. Qed.
Print Assumptions ibt_arr_ad.
Goal Logic.True. idtac "AUDIT_END ibt_arr_ad". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ibt_busy_interval_related". exact Logic.I. Qed.
Print Assumptions ibt_busy_interval_related.
Goal Logic.True. idtac "AUDIT_END ibt_busy_interval_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ibt_job_of_task_related". exact Logic.I. Qed.
Print Assumptions ibt_job_of_task_related.
Goal Logic.True. idtac "AUDIT_END ibt_job_of_task_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ibt_sched_at". exact Logic.I. Qed.
Print Assumptions ibt_sched_at.
Goal Logic.True. idtac "AUDIT_END ibt_sched_at". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ibt_service_at". exact Logic.I. Qed.
Print Assumptions ibt_service_at.
Goal Logic.True. idtac "AUDIT_END ibt_service_at". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ibt_completed". exact Logic.I. Qed.
Print Assumptions ibt_completed.
Goal Logic.True. idtac "AUDIT_END ibt_completed". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ibt_pending". exact Logic.I. Qed.
Print Assumptions ibt_pending.
Goal Logic.True. idtac "AUDIT_END ibt_pending". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ibt_come_from". exact Logic.I. Qed.
Print Assumptions ibt_come_from.
Goal Logic.True. idtac "AUDIT_END ibt_come_from". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ibt_is_idle". exact Logic.I. Qed.
Print Assumptions ibt_is_idle.
Goal Logic.True. idtac "AUDIT_END ibt_is_idle". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ibt_eq_identity". exact Logic.I. Qed.
Print Assumptions ibt_eq_identity.
Goal Logic.True. idtac "AUDIT_END ibt_eq_identity". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ibt_uni". exact Logic.I. Qed.
Print Assumptions ibt_uni.
Goal Logic.True. idtac "AUDIT_END ibt_uni". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ibt_forall_ma". exact Logic.I. Qed.
Print Assumptions ibt_forall_ma.
Goal Logic.True. idtac "AUDIT_END ibt_forall_ma". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ibt_taskset_respects". exact Logic.I. Qed.
Print Assumptions ibt_taskset_respects.
Goal Logic.True. idtac "AUDIT_END ibt_taskset_respects". exact Logic.I. Qed.
