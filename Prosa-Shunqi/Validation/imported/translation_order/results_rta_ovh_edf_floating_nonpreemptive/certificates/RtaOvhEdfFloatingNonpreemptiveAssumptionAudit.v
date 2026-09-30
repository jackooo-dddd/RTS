From FoundationCertificates Require Import
  OvhArrivalsSeqBaseAdapter OvhArrivalsSeqOperations OvhArrivalsSeqCorrespondence OvhArrivalsCorrespondence OvhJitterSvcBaseAdapter OvhJitterSvcNatBoolOperations OvhJitterSvcIntervalOperations OvhJitterSvcScheduleOperations OvhJitterSvcJobOperations OvhPreemptionParameterCorrespondence OvhPreemptionTimeCorrespondence OvhPriorityDrivenCorrespondence OvhPStateCoverHelpers OvhFactsPreemptionHelpers OvhWorkloadCorrespondence OvhPriorityInversionCorrespondence OvhExistenceHelpers OvhHepAtPtHelpers OvhTaskPreemptionParametersCorrespondence OvhBusyIntervalPiHelpers OvhStateRel OvhCurvesCorrespondence OvhRequestBoundFunctionCorrespondence OvhEdfAthepBoundCorrespondence OvhBlockingBoundEdfCorrespondence OvhSearchSpaceEdfCorrespondence OvhLimitedPreemptiveCorrespondence OvhTaskFloatingNonpreemptiveCorrespondence OvhEdfPiBoundCorrespondence ScheduleChangeBaseAdapter ScheduleChangeStateAdapter ScheduleChangeOptionOperations ScheduleChangeIntervalOperations ScheduleChangeListOperations ScheduleChangeCorrespondence OverheadsBaseAdapter OverheadsNatBoolOperations OverheadsIntervalOperations OverheadsCorrespondence OverheadResourceModelCorrespondence RtaOvhEdfFloatingNonpreemptiveCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN busy_window_recurrence_solution_correspondence". exact Logic.I. Qed.
Print Assumptions busy_window_recurrence_solution_correspondence.
Goal Logic.True. idtac "AUDIT_END busy_window_recurrence_solution_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rta_recurrence_solution_correspondence". exact Logic.I. Qed.
Print Assumptions rta_recurrence_solution_correspondence.
Goal Logic.True. idtac "AUDIT_END rta_recurrence_solution_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN uniprocessor_response_time_bound_floating_edf_correspondence". exact Logic.I. Qed.
Print Assumptions uniprocessor_response_time_bound_floating_edf_correspondence.
Goal Logic.True. idtac "AUDIT_END uniprocessor_response_time_bound_floating_edf_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roefl_task_cost_of_job_related". exact Logic.I. Qed.
Print Assumptions roefl_task_cost_of_job_related.
Goal Logic.True. idtac "AUDIT_END roefl_task_cost_of_job_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roefl_task_deadline_of_job_related". exact Logic.I. Qed.
Print Assumptions roefl_task_deadline_of_job_related.
Goal Logic.True. idtac "AUDIT_END roefl_task_deadline_of_job_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roefl_valid_job_costs_rel". exact Logic.I. Qed.
Print Assumptions roefl_valid_job_costs_rel.
Goal Logic.True. idtac "AUDIT_END roefl_valid_job_costs_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roefl_all_jobs_from_taskset_rel". exact Logic.I. Qed.
Print Assumptions roefl_all_jobs_from_taskset_rel.
Goal Logic.True. idtac "AUDIT_END roefl_all_jobs_from_taskset_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roefl_valid_task_arrival_sequence_rel". exact Logic.I. Qed.
Print Assumptions roefl_valid_task_arrival_sequence_rel.
Goal Logic.True. idtac "AUDIT_END roefl_valid_task_arrival_sequence_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roefl_positive_costs_rel". exact Logic.I. Qed.
Print Assumptions roefl_positive_costs_rel.
Goal Logic.True. idtac "AUDIT_END roefl_positive_costs_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roefl_ovh_sched". exact Logic.I. Qed.
Print Assumptions roefl_ovh_sched.
Goal Logic.True. idtac "AUDIT_END roefl_ovh_sched". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roefl_basic_ready_rel". exact Logic.I. Qed.
Print Assumptions roefl_basic_ready_rel.
Goal Logic.True. idtac "AUDIT_END roefl_basic_ready_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roefl_preempted_at_related". exact Logic.I. Qed.
Print Assumptions roefl_preempted_at_related.
Goal Logic.True. idtac "AUDIT_END roefl_preempted_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roefl_no_superfluous_rel". exact Logic.I. Qed.
Print Assumptions roefl_no_superfluous_rel.
Goal Logic.True. idtac "AUDIT_END roefl_no_superfluous_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roefl_edf_rel". exact Logic.I. Qed.
Print Assumptions roefl_edf_rel.
Goal Logic.True. idtac "AUDIT_END roefl_edf_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roefl_job_model_related". exact Logic.I. Qed.
Print Assumptions roefl_job_model_related.
Goal Logic.True. idtac "AUDIT_END roefl_job_model_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roefl_schedule_respects_rel". exact Logic.I. Qed.
Print Assumptions roefl_schedule_respects_rel.
Goal Logic.True. idtac "AUDIT_END roefl_schedule_respects_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roefl_job_of_task_related". exact Logic.I. Qed.
Print Assumptions roefl_job_of_task_related.
Goal Logic.True. idtac "AUDIT_END roefl_job_of_task_related". exact Logic.I. Qed.
