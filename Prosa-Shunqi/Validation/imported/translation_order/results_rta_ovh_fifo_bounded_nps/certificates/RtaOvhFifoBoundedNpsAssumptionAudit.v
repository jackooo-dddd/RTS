From FoundationCertificates Require Import
  OvhArrivalsSeqBaseAdapter OvhArrivalsSeqOperations OvhArrivalsSeqCorrespondence OvhArrivalsCorrespondence OvhJitterSvcBaseAdapter OvhJitterSvcNatBoolOperations OvhJitterSvcIntervalOperations OvhJitterSvcScheduleOperations OvhJitterSvcJobOperations OvhPreemptionParameterCorrespondence OvhPreemptionTimeCorrespondence OvhPriorityDrivenCorrespondence OvhPStateCoverHelpers OvhFactsPreemptionHelpers OvhWorkloadCorrespondence OvhPriorityInversionCorrespondence OvhExistenceHelpers OvhHepAtPtHelpers OvhTaskPreemptionParametersCorrespondence OvhBusyIntervalPiHelpers OvhStateRel OvhCurvesCorrespondence OvhRequestBoundFunctionCorrespondence OvhSearchSpaceFifoCorrespondence ScheduleChangeBaseAdapter ScheduleChangeStateAdapter ScheduleChangeOptionOperations ScheduleChangeIntervalOperations ScheduleChangeListOperations ScheduleChangeCorrespondence OverheadsBaseAdapter OverheadsNatBoolOperations OverheadsIntervalOperations OverheadsCorrespondence OverheadResourceModelCorrespondence RtaOvhFifoBoundedNpsCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN busy_window_recurrence_solution_correspondence". exact Logic.I. Qed.
Print Assumptions busy_window_recurrence_solution_correspondence.
Goal Logic.True. idtac "AUDIT_END busy_window_recurrence_solution_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rta_recurrence_solution_correspondence". exact Logic.I. Qed.
Print Assumptions rta_recurrence_solution_correspondence.
Goal Logic.True. idtac "AUDIT_END rta_recurrence_solution_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN uniprocessor_response_time_bound_fifo_correspondence". exact Logic.I. Qed.
Print Assumptions uniprocessor_response_time_bound_fifo_correspondence.
Goal Logic.True. idtac "AUDIT_END uniprocessor_response_time_bound_fifo_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rof_task_cost_of_job_related". exact Logic.I. Qed.
Print Assumptions rof_task_cost_of_job_related.
Goal Logic.True. idtac "AUDIT_END rof_task_cost_of_job_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rof_valid_job_costs_rel". exact Logic.I. Qed.
Print Assumptions rof_valid_job_costs_rel.
Goal Logic.True. idtac "AUDIT_END rof_valid_job_costs_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rof_all_jobs_from_taskset_rel". exact Logic.I. Qed.
Print Assumptions rof_all_jobs_from_taskset_rel.
Goal Logic.True. idtac "AUDIT_END rof_all_jobs_from_taskset_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rof_valid_task_arrival_sequence_rel". exact Logic.I. Qed.
Print Assumptions rof_valid_task_arrival_sequence_rel.
Goal Logic.True. idtac "AUDIT_END rof_valid_task_arrival_sequence_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rof_positive_costs_rel". exact Logic.I. Qed.
Print Assumptions rof_positive_costs_rel.
Goal Logic.True. idtac "AUDIT_END rof_positive_costs_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rof_ovh_sched". exact Logic.I. Qed.
Print Assumptions rof_ovh_sched.
Goal Logic.True. idtac "AUDIT_END rof_ovh_sched". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rof_basic_ready_rel". exact Logic.I. Qed.
Print Assumptions rof_basic_ready_rel.
Goal Logic.True. idtac "AUDIT_END rof_basic_ready_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rof_preempted_at_related". exact Logic.I. Qed.
Print Assumptions rof_preempted_at_related.
Goal Logic.True. idtac "AUDIT_END rof_preempted_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rof_no_superfluous_rel". exact Logic.I. Qed.
Print Assumptions rof_no_superfluous_rel.
Goal Logic.True. idtac "AUDIT_END rof_no_superfluous_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rof_fifo_rel". exact Logic.I. Qed.
Print Assumptions rof_fifo_rel.
Goal Logic.True. idtac "AUDIT_END rof_fifo_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rof_job_of_task_related". exact Logic.I. Qed.
Print Assumptions rof_job_of_task_related.
Goal Logic.True. idtac "AUDIT_END rof_job_of_task_related". exact Logic.I. Qed.
