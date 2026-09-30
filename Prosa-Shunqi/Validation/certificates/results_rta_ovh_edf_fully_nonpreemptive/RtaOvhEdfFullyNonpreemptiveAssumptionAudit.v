From FoundationCertificates Require Import
  OvhArrivalsSeqBaseAdapter OvhArrivalsSeqOperations OvhArrivalsSeqCorrespondence OvhArrivalsCorrespondence OvhJitterSvcBaseAdapter OvhJitterSvcNatBoolOperations OvhJitterSvcIntervalOperations OvhJitterSvcScheduleOperations OvhJitterSvcJobOperations OvhPreemptionParameterCorrespondence OvhPreemptionTimeCorrespondence OvhPriorityDrivenCorrespondence OvhPStateCoverHelpers OvhFactsPreemptionHelpers OvhWorkloadCorrespondence OvhPriorityInversionCorrespondence OvhExistenceHelpers OvhHepAtPtHelpers OvhTaskPreemptionParametersCorrespondence OvhBusyIntervalPiHelpers OvhStateRel OvhCurvesCorrespondence OvhRequestBoundFunctionCorrespondence OvhEdfAthepBoundCorrespondence OvhBlockingBoundEdfCorrespondence OvhSearchSpaceEdfCorrespondence OvhEdfPiBoundCorrespondence ScheduleChangeBaseAdapter ScheduleChangeStateAdapter ScheduleChangeOptionOperations ScheduleChangeIntervalOperations ScheduleChangeListOperations ScheduleChangeCorrespondence OverheadsBaseAdapter OverheadsNatBoolOperations OverheadsIntervalOperations OverheadsCorrespondence OverheadResourceModelCorrespondence RtaOvhEdfFullyNonpreemptiveCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN busy_window_recurrence_solution_correspondence". exact Logic.I. Qed.
Print Assumptions busy_window_recurrence_solution_correspondence.
Goal Logic.True. idtac "AUDIT_END busy_window_recurrence_solution_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rta_recurrence_solution_correspondence". exact Logic.I. Qed.
Print Assumptions rta_recurrence_solution_correspondence.
Goal Logic.True. idtac "AUDIT_END rta_recurrence_solution_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN uniprocessor_response_time_bound_fully_nonpreemptive_edf_correspondence". exact Logic.I. Qed.
Print Assumptions uniprocessor_response_time_bound_fully_nonpreemptive_edf_correspondence.
Goal Logic.True. idtac "AUDIT_END uniprocessor_response_time_bound_fully_nonpreemptive_edf_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roenp_task_cost_of_job_related". exact Logic.I. Qed.
Print Assumptions roenp_task_cost_of_job_related.
Goal Logic.True. idtac "AUDIT_END roenp_task_cost_of_job_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roenp_task_deadline_of_job_related". exact Logic.I. Qed.
Print Assumptions roenp_task_deadline_of_job_related.
Goal Logic.True. idtac "AUDIT_END roenp_task_deadline_of_job_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roenp_task_model_related". exact Logic.I. Qed.
Print Assumptions roenp_task_model_related.
Goal Logic.True. idtac "AUDIT_END roenp_task_model_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roenp_valid_job_costs_rel". exact Logic.I. Qed.
Print Assumptions roenp_valid_job_costs_rel.
Goal Logic.True. idtac "AUDIT_END roenp_valid_job_costs_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roenp_all_jobs_from_taskset_rel". exact Logic.I. Qed.
Print Assumptions roenp_all_jobs_from_taskset_rel.
Goal Logic.True. idtac "AUDIT_END roenp_all_jobs_from_taskset_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roenp_valid_task_arrival_sequence_rel". exact Logic.I. Qed.
Print Assumptions roenp_valid_task_arrival_sequence_rel.
Goal Logic.True. idtac "AUDIT_END roenp_valid_task_arrival_sequence_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roenp_positive_costs_rel". exact Logic.I. Qed.
Print Assumptions roenp_positive_costs_rel.
Goal Logic.True. idtac "AUDIT_END roenp_positive_costs_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roenp_ovh_sched". exact Logic.I. Qed.
Print Assumptions roenp_ovh_sched.
Goal Logic.True. idtac "AUDIT_END roenp_ovh_sched". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roenp_basic_ready_rel". exact Logic.I. Qed.
Print Assumptions roenp_basic_ready_rel.
Goal Logic.True. idtac "AUDIT_END roenp_basic_ready_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roenp_preempted_at_related". exact Logic.I. Qed.
Print Assumptions roenp_preempted_at_related.
Goal Logic.True. idtac "AUDIT_END roenp_preempted_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roenp_no_superfluous_rel". exact Logic.I. Qed.
Print Assumptions roenp_no_superfluous_rel.
Goal Logic.True. idtac "AUDIT_END roenp_no_superfluous_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roenp_edf_rel". exact Logic.I. Qed.
Print Assumptions roenp_edf_rel.
Goal Logic.True. idtac "AUDIT_END roenp_edf_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roenp_job_model_related". exact Logic.I. Qed.
Print Assumptions roenp_job_model_related.
Goal Logic.True. idtac "AUDIT_END roenp_job_model_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roenp_nonpreemptive_schedule_rel". exact Logic.I. Qed.
Print Assumptions roenp_nonpreemptive_schedule_rel.
Goal Logic.True. idtac "AUDIT_END roenp_nonpreemptive_schedule_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roenp_job_of_task_related". exact Logic.I. Qed.
Print Assumptions roenp_job_of_task_related.
Goal Logic.True. idtac "AUDIT_END roenp_job_of_task_related". exact Logic.I. Qed.
