From FoundationCertificates Require Import
  OvhArrivalsSeqBaseAdapter OvhArrivalsSeqOperations OvhArrivalsSeqCorrespondence OvhArrivalsCorrespondence OvhJitterSvcBaseAdapter OvhJitterSvcNatBoolOperations OvhJitterSvcIntervalOperations OvhJitterSvcScheduleOperations OvhJitterSvcJobOperations OvhPreemptionParameterCorrespondence OvhPreemptionTimeCorrespondence OvhPriorityDrivenCorrespondence OvhPStateCoverHelpers OvhFactsPreemptionHelpers OvhWorkloadCorrespondence OvhPriorityInversionCorrespondence OvhExistenceHelpers OvhHepAtPtHelpers OvhTaskPreemptionParametersCorrespondence OvhBusyIntervalPiHelpers OvhStateRel OvhCurvesCorrespondence OvhRequestBoundFunctionCorrespondence OvhBlockingBoundFpCorrespondence OvhSearchSpaceFpCorrespondence ScheduleChangeBaseAdapter ScheduleChangeStateAdapter ScheduleChangeOptionOperations ScheduleChangeIntervalOperations ScheduleChangeListOperations ScheduleChangeCorrespondence OverheadsBaseAdapter OverheadsNatBoolOperations OverheadsIntervalOperations OverheadsCorrespondence OverheadResourceModelCorrespondence RtaOvhFpFullyPreemptiveCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN busy_window_recurrence_solution_correspondence". exact Logic.I. Qed.
Print Assumptions busy_window_recurrence_solution_correspondence.
Goal Logic.True. idtac "AUDIT_END busy_window_recurrence_solution_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rta_recurrence_solution_correspondence". exact Logic.I. Qed.
Print Assumptions rta_recurrence_solution_correspondence.
Goal Logic.True. idtac "AUDIT_END rta_recurrence_solution_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN uniprocessor_response_time_bound_fully_preemptive_fp_correspondence". exact Logic.I. Qed.
Print Assumptions uniprocessor_response_time_bound_fully_preemptive_fp_correspondence.
Goal Logic.True. idtac "AUDIT_END uniprocessor_response_time_bound_fully_preemptive_fp_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roffp_task_cost_of_job_related". exact Logic.I. Qed.
Print Assumptions roffp_task_cost_of_job_related.
Goal Logic.True. idtac "AUDIT_END roffp_task_cost_of_job_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roffp_valid_job_costs_rel". exact Logic.I. Qed.
Print Assumptions roffp_valid_job_costs_rel.
Goal Logic.True. idtac "AUDIT_END roffp_valid_job_costs_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roffp_all_jobs_from_taskset_rel". exact Logic.I. Qed.
Print Assumptions roffp_all_jobs_from_taskset_rel.
Goal Logic.True. idtac "AUDIT_END roffp_all_jobs_from_taskset_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roffp_valid_task_arrival_sequence_rel". exact Logic.I. Qed.
Print Assumptions roffp_valid_task_arrival_sequence_rel.
Goal Logic.True. idtac "AUDIT_END roffp_valid_task_arrival_sequence_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roffp_positive_costs_rel". exact Logic.I. Qed.
Print Assumptions roffp_positive_costs_rel.
Goal Logic.True. idtac "AUDIT_END roffp_positive_costs_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roffp_ovh_sched". exact Logic.I. Qed.
Print Assumptions roffp_ovh_sched.
Goal Logic.True. idtac "AUDIT_END roffp_ovh_sched". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roffp_basic_ready_rel". exact Logic.I. Qed.
Print Assumptions roffp_basic_ready_rel.
Goal Logic.True. idtac "AUDIT_END roffp_basic_ready_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roffp_preempted_at_related". exact Logic.I. Qed.
Print Assumptions roffp_preempted_at_related.
Goal Logic.True. idtac "AUDIT_END roffp_preempted_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roffp_no_superfluous_rel". exact Logic.I. Qed.
Print Assumptions roffp_no_superfluous_rel.
Goal Logic.True. idtac "AUDIT_END roffp_no_superfluous_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roffp_forall_fp". exact Logic.I. Qed.
Print Assumptions roffp_forall_fp.
Goal Logic.True. idtac "AUDIT_END roffp_forall_fp". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roffp_reflexive_task_rel". exact Logic.I. Qed.
Print Assumptions roffp_reflexive_task_rel.
Goal Logic.True. idtac "AUDIT_END roffp_reflexive_task_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roffp_transitive_task_rel". exact Logic.I. Qed.
Print Assumptions roffp_transitive_task_rel.
Goal Logic.True. idtac "AUDIT_END roffp_transitive_task_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roffp_fp_hep_job_related". exact Logic.I. Qed.
Print Assumptions roffp_fp_hep_job_related.
Goal Logic.True. idtac "AUDIT_END roffp_fp_hep_job_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roffp_same_task_related". exact Logic.I. Qed.
Print Assumptions roffp_same_task_related.
Goal Logic.True. idtac "AUDIT_END roffp_same_task_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roffp_sequential_tasks_rel". exact Logic.I. Qed.
Print Assumptions roffp_sequential_tasks_rel.
Goal Logic.True. idtac "AUDIT_END roffp_sequential_tasks_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roffp_fully_preemptive_job_related". exact Logic.I. Qed.
Print Assumptions roffp_fully_preemptive_job_related.
Goal Logic.True. idtac "AUDIT_END roffp_fully_preemptive_job_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roffp_job_of_task_related". exact Logic.I. Qed.
Print Assumptions roffp_job_of_task_related.
Goal Logic.True. idtac "AUDIT_END roffp_job_of_task_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roffp_sum_filter_related". exact Logic.I. Qed.
Print Assumptions roffp_sum_filter_related.
Goal Logic.True. idtac "AUDIT_END roffp_sum_filter_related". exact Logic.I. Qed.
