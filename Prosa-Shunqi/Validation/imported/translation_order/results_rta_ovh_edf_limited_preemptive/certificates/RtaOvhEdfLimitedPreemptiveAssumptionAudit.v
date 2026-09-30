From FoundationCertificates Require Import
  OvhArrivalsSeqBaseAdapter OvhArrivalsSeqOperations OvhArrivalsSeqCorrespondence OvhArrivalsCorrespondence OvhJitterSvcBaseAdapter OvhJitterSvcNatBoolOperations OvhJitterSvcIntervalOperations OvhJitterSvcScheduleOperations OvhJitterSvcJobOperations OvhPreemptionParameterCorrespondence OvhPreemptionTimeCorrespondence OvhPriorityDrivenCorrespondence OvhPStateCoverHelpers OvhFactsPreemptionHelpers OvhWorkloadCorrespondence OvhPriorityInversionCorrespondence OvhExistenceHelpers OvhHepAtPtHelpers OvhTaskPreemptionParametersCorrespondence OvhBusyIntervalPiHelpers OvhStateRel OvhCurvesCorrespondence OvhRequestBoundFunctionCorrespondence OvhEdfAthepBoundCorrespondence OvhBlockingBoundEdfCorrespondence OvhSearchSpaceEdfCorrespondence OvhLimitedPreemptiveCorrespondence OvhTaskLimitedPreemptiveCorrespondence OvhEdfPiBoundCorrespondence ScheduleChangeBaseAdapter ScheduleChangeStateAdapter ScheduleChangeOptionOperations ScheduleChangeIntervalOperations ScheduleChangeListOperations ScheduleChangeCorrespondence OverheadsBaseAdapter OverheadsNatBoolOperations OverheadsIntervalOperations OverheadsCorrespondence OverheadResourceModelCorrespondence RtaOvhEdfLimitedPreemptiveCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN busy_window_recurrence_solution_correspondence". exact Logic.I. Qed.
Print Assumptions busy_window_recurrence_solution_correspondence.
Goal Logic.True. idtac "AUDIT_END busy_window_recurrence_solution_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rta_recurrence_solution_correspondence". exact Logic.I. Qed.
Print Assumptions rta_recurrence_solution_correspondence.
Goal Logic.True. idtac "AUDIT_END rta_recurrence_solution_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN uniprocessor_response_time_bound_limited_edf_correspondence". exact Logic.I. Qed.
Print Assumptions uniprocessor_response_time_bound_limited_edf_correspondence.
Goal Logic.True. idtac "AUDIT_END uniprocessor_response_time_bound_limited_edf_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roelp_task_cost_of_job_related". exact Logic.I. Qed.
Print Assumptions roelp_task_cost_of_job_related.
Goal Logic.True. idtac "AUDIT_END roelp_task_cost_of_job_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roelp_task_deadline_of_job_related". exact Logic.I. Qed.
Print Assumptions roelp_task_deadline_of_job_related.
Goal Logic.True. idtac "AUDIT_END roelp_task_deadline_of_job_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roelp_valid_job_costs_rel". exact Logic.I. Qed.
Print Assumptions roelp_valid_job_costs_rel.
Goal Logic.True. idtac "AUDIT_END roelp_valid_job_costs_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roelp_all_jobs_from_taskset_rel". exact Logic.I. Qed.
Print Assumptions roelp_all_jobs_from_taskset_rel.
Goal Logic.True. idtac "AUDIT_END roelp_all_jobs_from_taskset_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roelp_valid_task_arrival_sequence_rel". exact Logic.I. Qed.
Print Assumptions roelp_valid_task_arrival_sequence_rel.
Goal Logic.True. idtac "AUDIT_END roelp_valid_task_arrival_sequence_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roelp_positive_costs_rel". exact Logic.I. Qed.
Print Assumptions roelp_positive_costs_rel.
Goal Logic.True. idtac "AUDIT_END roelp_positive_costs_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roelp_ovh_sched". exact Logic.I. Qed.
Print Assumptions roelp_ovh_sched.
Goal Logic.True. idtac "AUDIT_END roelp_ovh_sched". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roelp_basic_ready_rel". exact Logic.I. Qed.
Print Assumptions roelp_basic_ready_rel.
Goal Logic.True. idtac "AUDIT_END roelp_basic_ready_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roelp_preempted_at_related". exact Logic.I. Qed.
Print Assumptions roelp_preempted_at_related.
Goal Logic.True. idtac "AUDIT_END roelp_preempted_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roelp_no_superfluous_rel". exact Logic.I. Qed.
Print Assumptions roelp_no_superfluous_rel.
Goal Logic.True. idtac "AUDIT_END roelp_no_superfluous_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roelp_edf_rel". exact Logic.I. Qed.
Print Assumptions roelp_edf_rel.
Goal Logic.True. idtac "AUDIT_END roelp_edf_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roelp_job_model_related". exact Logic.I. Qed.
Print Assumptions roelp_job_model_related.
Goal Logic.True. idtac "AUDIT_END roelp_job_model_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roelp_schedule_respects_rel". exact Logic.I. Qed.
Print Assumptions roelp_schedule_respects_rel.
Goal Logic.True. idtac "AUDIT_END roelp_schedule_respects_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roelp_job_of_task_related". exact Logic.I. Qed.
Print Assumptions roelp_job_of_task_related.
Goal Logic.True. idtac "AUDIT_END roelp_job_of_task_related". exact Logic.I. Qed.
