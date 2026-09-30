From FoundationCertificates Require Import
  OvhArrivalsSeqBaseAdapter OvhArrivalsSeqOperations OvhArrivalsSeqCorrespondence OvhArrivalsCorrespondence OvhJitterSvcBaseAdapter OvhJitterSvcNatBoolOperations OvhJitterSvcIntervalOperations OvhJitterSvcScheduleOperations OvhJitterSvcJobOperations OvhPreemptionParameterCorrespondence OvhPreemptionTimeCorrespondence OvhPriorityDrivenCorrespondence OvhPStateCoverHelpers OvhFactsPreemptionHelpers OvhWorkloadCorrespondence OvhPriorityInversionCorrespondence OvhExistenceHelpers OvhHepAtPtHelpers OvhTaskPreemptionParametersCorrespondence OvhBusyIntervalPiHelpers OvhStateRel OvhCurvesCorrespondence OvhRequestBoundFunctionCorrespondence OvhEdfAthepBoundCorrespondence OvhBlockingBoundEdfCorrespondence OvhSearchSpaceEdfCorrespondence ScheduleChangeBaseAdapter ScheduleChangeStateAdapter ScheduleChangeOptionOperations ScheduleChangeIntervalOperations ScheduleChangeListOperations ScheduleChangeCorrespondence OverheadsBaseAdapter OverheadsNatBoolOperations OverheadsIntervalOperations OverheadsCorrespondence OverheadResourceModelCorrespondence RtaOvhEdfFullyPreemptiveCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN busy_window_recurrence_solution_correspondence". exact Logic.I. Qed.
Print Assumptions busy_window_recurrence_solution_correspondence.
Goal Logic.True. idtac "AUDIT_END busy_window_recurrence_solution_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rta_recurrence_solution_correspondence". exact Logic.I. Qed.
Print Assumptions rta_recurrence_solution_correspondence.
Goal Logic.True. idtac "AUDIT_END rta_recurrence_solution_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN uniprocessor_response_time_bound_fully_preemptive_edf_correspondence". exact Logic.I. Qed.
Print Assumptions uniprocessor_response_time_bound_fully_preemptive_edf_correspondence.
Goal Logic.True. idtac "AUDIT_END uniprocessor_response_time_bound_fully_preemptive_edf_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roefp_task_cost_of_job_related". exact Logic.I. Qed.
Print Assumptions roefp_task_cost_of_job_related.
Goal Logic.True. idtac "AUDIT_END roefp_task_cost_of_job_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roefp_task_deadline_of_job_related". exact Logic.I. Qed.
Print Assumptions roefp_task_deadline_of_job_related.
Goal Logic.True. idtac "AUDIT_END roefp_task_deadline_of_job_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roefp_task_model_related". exact Logic.I. Qed.
Print Assumptions roefp_task_model_related.
Goal Logic.True. idtac "AUDIT_END roefp_task_model_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roefp_valid_job_costs_rel". exact Logic.I. Qed.
Print Assumptions roefp_valid_job_costs_rel.
Goal Logic.True. idtac "AUDIT_END roefp_valid_job_costs_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roefp_all_jobs_from_taskset_rel". exact Logic.I. Qed.
Print Assumptions roefp_all_jobs_from_taskset_rel.
Goal Logic.True. idtac "AUDIT_END roefp_all_jobs_from_taskset_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roefp_valid_task_arrival_sequence_rel". exact Logic.I. Qed.
Print Assumptions roefp_valid_task_arrival_sequence_rel.
Goal Logic.True. idtac "AUDIT_END roefp_valid_task_arrival_sequence_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roefp_positive_costs_rel". exact Logic.I. Qed.
Print Assumptions roefp_positive_costs_rel.
Goal Logic.True. idtac "AUDIT_END roefp_positive_costs_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roefp_ovh_sched". exact Logic.I. Qed.
Print Assumptions roefp_ovh_sched.
Goal Logic.True. idtac "AUDIT_END roefp_ovh_sched". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roefp_basic_ready_rel". exact Logic.I. Qed.
Print Assumptions roefp_basic_ready_rel.
Goal Logic.True. idtac "AUDIT_END roefp_basic_ready_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roefp_preempted_at_related". exact Logic.I. Qed.
Print Assumptions roefp_preempted_at_related.
Goal Logic.True. idtac "AUDIT_END roefp_preempted_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roefp_no_superfluous_rel". exact Logic.I. Qed.
Print Assumptions roefp_no_superfluous_rel.
Goal Logic.True. idtac "AUDIT_END roefp_no_superfluous_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roefp_edf_rel". exact Logic.I. Qed.
Print Assumptions roefp_edf_rel.
Goal Logic.True. idtac "AUDIT_END roefp_edf_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roefp_fully_preemptive_job_related". exact Logic.I. Qed.
Print Assumptions roefp_fully_preemptive_job_related.
Goal Logic.True. idtac "AUDIT_END roefp_fully_preemptive_job_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN roefp_job_of_task_related". exact Logic.I. Qed.
Print Assumptions roefp_job_of_task_related.
Goal Logic.True. idtac "AUDIT_END roefp_job_of_task_related". exact Logic.I. Qed.
