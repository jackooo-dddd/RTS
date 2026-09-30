From FoundationCertificates Require Import
  OvhArrivalsSeqBaseAdapter OvhArrivalsSeqOperations OvhArrivalsSeqCorrespondence OvhArrivalsCorrespondence OvhJitterSvcBaseAdapter OvhJitterSvcNatBoolOperations OvhJitterSvcIntervalOperations OvhJitterSvcScheduleOperations OvhJitterSvcJobOperations OvhPreemptionParameterCorrespondence OvhPreemptionTimeCorrespondence OvhPriorityDrivenCorrespondence OvhPStateCoverHelpers OvhFactsPreemptionHelpers OvhWorkloadCorrespondence OvhPriorityInversionCorrespondence OvhExistenceHelpers OvhHepAtPtHelpers OvhTaskPreemptionParametersCorrespondence OvhBusyIntervalPiHelpers OvhStateRel OvhCurvesCorrespondence OvhRequestBoundFunctionCorrespondence OvhBlockingBoundFpCorrespondence OvhSearchSpaceFpCorrespondence OvhLimitedPreemptiveCorrespondence OvhTaskLimitedPreemptiveCorrespondence ScheduleChangeBaseAdapter ScheduleChangeStateAdapter ScheduleChangeOptionOperations ScheduleChangeIntervalOperations ScheduleChangeListOperations ScheduleChangeCorrespondence OverheadsBaseAdapter OverheadsNatBoolOperations OverheadsIntervalOperations OverheadsCorrespondence OverheadResourceModelCorrespondence RtaOvhFpLimitedPreemptiveCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN busy_window_recurrence_solution_correspondence". exact Logic.I. Qed.
Print Assumptions busy_window_recurrence_solution_correspondence.
Goal Logic.True. idtac "AUDIT_END busy_window_recurrence_solution_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rta_recurrence_solution_correspondence". exact Logic.I. Qed.
Print Assumptions rta_recurrence_solution_correspondence.
Goal Logic.True. idtac "AUDIT_END rta_recurrence_solution_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN uniprocessor_response_time_bound_limited_fp_correspondence". exact Logic.I. Qed.
Print Assumptions uniprocessor_response_time_bound_limited_fp_correspondence.
Goal Logic.True. idtac "AUDIT_END uniprocessor_response_time_bound_limited_fp_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roflp_task_cost_of_job_related". exact Logic.I. Qed.
Print Assumptions roflp_task_cost_of_job_related.
Goal Logic.True. idtac "AUDIT_END roflp_task_cost_of_job_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roflp_valid_job_costs_rel". exact Logic.I. Qed.
Print Assumptions roflp_valid_job_costs_rel.
Goal Logic.True. idtac "AUDIT_END roflp_valid_job_costs_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roflp_all_jobs_from_taskset_rel". exact Logic.I. Qed.
Print Assumptions roflp_all_jobs_from_taskset_rel.
Goal Logic.True. idtac "AUDIT_END roflp_all_jobs_from_taskset_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roflp_valid_task_arrival_sequence_rel". exact Logic.I. Qed.
Print Assumptions roflp_valid_task_arrival_sequence_rel.
Goal Logic.True. idtac "AUDIT_END roflp_valid_task_arrival_sequence_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roflp_positive_costs_rel". exact Logic.I. Qed.
Print Assumptions roflp_positive_costs_rel.
Goal Logic.True. idtac "AUDIT_END roflp_positive_costs_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roflp_ovh_sched". exact Logic.I. Qed.
Print Assumptions roflp_ovh_sched.
Goal Logic.True. idtac "AUDIT_END roflp_ovh_sched". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roflp_basic_ready_rel". exact Logic.I. Qed.
Print Assumptions roflp_basic_ready_rel.
Goal Logic.True. idtac "AUDIT_END roflp_basic_ready_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roflp_preempted_at_related". exact Logic.I. Qed.
Print Assumptions roflp_preempted_at_related.
Goal Logic.True. idtac "AUDIT_END roflp_preempted_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roflp_no_superfluous_rel". exact Logic.I. Qed.
Print Assumptions roflp_no_superfluous_rel.
Goal Logic.True. idtac "AUDIT_END roflp_no_superfluous_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roflp_forall_fp". exact Logic.I. Qed.
Print Assumptions roflp_forall_fp.
Goal Logic.True. idtac "AUDIT_END roflp_forall_fp". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roflp_reflexive_task_rel". exact Logic.I. Qed.
Print Assumptions roflp_reflexive_task_rel.
Goal Logic.True. idtac "AUDIT_END roflp_reflexive_task_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roflp_transitive_task_rel". exact Logic.I. Qed.
Print Assumptions roflp_transitive_task_rel.
Goal Logic.True. idtac "AUDIT_END roflp_transitive_task_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roflp_fp_hep_job_related". exact Logic.I. Qed.
Print Assumptions roflp_fp_hep_job_related.
Goal Logic.True. idtac "AUDIT_END roflp_fp_hep_job_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roflp_same_task_related". exact Logic.I. Qed.
Print Assumptions roflp_same_task_related.
Goal Logic.True. idtac "AUDIT_END roflp_same_task_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roflp_sequential_tasks_rel". exact Logic.I. Qed.
Print Assumptions roflp_sequential_tasks_rel.
Goal Logic.True. idtac "AUDIT_END roflp_sequential_tasks_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roflp_job_model_related". exact Logic.I. Qed.
Print Assumptions roflp_job_model_related.
Goal Logic.True. idtac "AUDIT_END roflp_job_model_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roflp_schedule_respects_rel". exact Logic.I. Qed.
Print Assumptions roflp_schedule_respects_rel.
Goal Logic.True. idtac "AUDIT_END roflp_schedule_respects_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roflp_job_of_task_related". exact Logic.I. Qed.
Print Assumptions roflp_job_of_task_related.
Goal Logic.True. idtac "AUDIT_END roflp_job_of_task_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roflp_sum_filter_related". exact Logic.I. Qed.
Print Assumptions roflp_sum_filter_related.
Goal Logic.True. idtac "AUDIT_END roflp_sum_filter_related". exact Logic.I. Qed.
