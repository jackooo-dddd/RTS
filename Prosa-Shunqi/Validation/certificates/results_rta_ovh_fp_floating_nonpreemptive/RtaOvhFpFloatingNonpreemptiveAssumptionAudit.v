From FoundationCertificates Require Import
  OvhArrivalsSeqBaseAdapter OvhArrivalsSeqOperations OvhArrivalsSeqCorrespondence OvhArrivalsCorrespondence OvhJitterSvcBaseAdapter OvhJitterSvcNatBoolOperations OvhJitterSvcIntervalOperations OvhJitterSvcScheduleOperations OvhJitterSvcJobOperations OvhPreemptionParameterCorrespondence OvhPreemptionTimeCorrespondence OvhPriorityDrivenCorrespondence OvhPStateCoverHelpers OvhFactsPreemptionHelpers OvhWorkloadCorrespondence OvhPriorityInversionCorrespondence OvhExistenceHelpers OvhHepAtPtHelpers OvhTaskPreemptionParametersCorrespondence OvhBusyIntervalPiHelpers OvhStateRel OvhCurvesCorrespondence OvhRequestBoundFunctionCorrespondence OvhBlockingBoundFpCorrespondence OvhSearchSpaceFpCorrespondence OvhLimitedPreemptiveCorrespondence OvhTaskFloatingNonpreemptiveCorrespondence ScheduleChangeBaseAdapter ScheduleChangeStateAdapter ScheduleChangeOptionOperations ScheduleChangeIntervalOperations ScheduleChangeListOperations ScheduleChangeCorrespondence OverheadsBaseAdapter OverheadsNatBoolOperations OverheadsIntervalOperations OverheadsCorrespondence OverheadResourceModelCorrespondence RtaOvhFpFloatingNonpreemptiveCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN busy_window_recurrence_solution_correspondence". exact Logic.I. Qed.
Print Assumptions busy_window_recurrence_solution_correspondence.
Goal Logic.True. idtac "AUDIT_END busy_window_recurrence_solution_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rta_recurrence_solution_correspondence". exact Logic.I. Qed.
Print Assumptions rta_recurrence_solution_correspondence.
Goal Logic.True. idtac "AUDIT_END rta_recurrence_solution_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN uniprocessor_response_time_bound_floating_fp_correspondence". exact Logic.I. Qed.
Print Assumptions uniprocessor_response_time_bound_floating_fp_correspondence.
Goal Logic.True. idtac "AUDIT_END uniprocessor_response_time_bound_floating_fp_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rofflt_task_cost_of_job_related". exact Logic.I. Qed.
Print Assumptions rofflt_task_cost_of_job_related.
Goal Logic.True. idtac "AUDIT_END rofflt_task_cost_of_job_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rofflt_valid_job_costs_rel". exact Logic.I. Qed.
Print Assumptions rofflt_valid_job_costs_rel.
Goal Logic.True. idtac "AUDIT_END rofflt_valid_job_costs_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rofflt_all_jobs_from_taskset_rel". exact Logic.I. Qed.
Print Assumptions rofflt_all_jobs_from_taskset_rel.
Goal Logic.True. idtac "AUDIT_END rofflt_all_jobs_from_taskset_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rofflt_valid_task_arrival_sequence_rel". exact Logic.I. Qed.
Print Assumptions rofflt_valid_task_arrival_sequence_rel.
Goal Logic.True. idtac "AUDIT_END rofflt_valid_task_arrival_sequence_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rofflt_positive_costs_rel". exact Logic.I. Qed.
Print Assumptions rofflt_positive_costs_rel.
Goal Logic.True. idtac "AUDIT_END rofflt_positive_costs_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rofflt_ovh_sched". exact Logic.I. Qed.
Print Assumptions rofflt_ovh_sched.
Goal Logic.True. idtac "AUDIT_END rofflt_ovh_sched". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rofflt_basic_ready_rel". exact Logic.I. Qed.
Print Assumptions rofflt_basic_ready_rel.
Goal Logic.True. idtac "AUDIT_END rofflt_basic_ready_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rofflt_preempted_at_related". exact Logic.I. Qed.
Print Assumptions rofflt_preempted_at_related.
Goal Logic.True. idtac "AUDIT_END rofflt_preempted_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rofflt_no_superfluous_rel". exact Logic.I. Qed.
Print Assumptions rofflt_no_superfluous_rel.
Goal Logic.True. idtac "AUDIT_END rofflt_no_superfluous_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rofflt_forall_fp". exact Logic.I. Qed.
Print Assumptions rofflt_forall_fp.
Goal Logic.True. idtac "AUDIT_END rofflt_forall_fp". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rofflt_reflexive_task_rel". exact Logic.I. Qed.
Print Assumptions rofflt_reflexive_task_rel.
Goal Logic.True. idtac "AUDIT_END rofflt_reflexive_task_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rofflt_transitive_task_rel". exact Logic.I. Qed.
Print Assumptions rofflt_transitive_task_rel.
Goal Logic.True. idtac "AUDIT_END rofflt_transitive_task_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rofflt_fp_hep_job_related". exact Logic.I. Qed.
Print Assumptions rofflt_fp_hep_job_related.
Goal Logic.True. idtac "AUDIT_END rofflt_fp_hep_job_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rofflt_same_task_related". exact Logic.I. Qed.
Print Assumptions rofflt_same_task_related.
Goal Logic.True. idtac "AUDIT_END rofflt_same_task_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rofflt_sequential_tasks_rel". exact Logic.I. Qed.
Print Assumptions rofflt_sequential_tasks_rel.
Goal Logic.True. idtac "AUDIT_END rofflt_sequential_tasks_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rofflt_job_model_related". exact Logic.I. Qed.
Print Assumptions rofflt_job_model_related.
Goal Logic.True. idtac "AUDIT_END rofflt_job_model_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rofflt_schedule_respects_rel". exact Logic.I. Qed.
Print Assumptions rofflt_schedule_respects_rel.
Goal Logic.True. idtac "AUDIT_END rofflt_schedule_respects_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rofflt_job_of_task_related". exact Logic.I. Qed.
Print Assumptions rofflt_job_of_task_related.
Goal Logic.True. idtac "AUDIT_END rofflt_job_of_task_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rofflt_sum_filter_related". exact Logic.I. Qed.
Print Assumptions rofflt_sum_filter_related.
Goal Logic.True. idtac "AUDIT_END rofflt_sum_filter_related". exact Logic.I. Qed.
