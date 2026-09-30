From FoundationCertificates Require Import
  OvhArrivalsSeqBaseAdapter OvhArrivalsSeqOperations OvhArrivalsSeqCorrespondence OvhArrivalsCorrespondence OvhJitterSvcBaseAdapter OvhJitterSvcNatBoolOperations OvhJitterSvcIntervalOperations OvhJitterSvcScheduleOperations OvhJitterSvcJobOperations OvhPreemptionParameterCorrespondence OvhPreemptionTimeCorrespondence OvhPriorityDrivenCorrespondence OvhPStateCoverHelpers OvhFactsPreemptionHelpers OvhWorkloadCorrespondence OvhPriorityInversionCorrespondence OvhExistenceHelpers OvhHepAtPtHelpers OvhTaskPreemptionParametersCorrespondence OvhBusyIntervalPiHelpers OvhStateRel OvhCurvesCorrespondence OvhRequestBoundFunctionCorrespondence OvhBlockingBoundFpCorrespondence OvhSearchSpaceFpCorrespondence ScheduleChangeBaseAdapter ScheduleChangeStateAdapter ScheduleChangeOptionOperations ScheduleChangeIntervalOperations ScheduleChangeListOperations ScheduleChangeCorrespondence OverheadsBaseAdapter OverheadsNatBoolOperations OverheadsIntervalOperations OverheadsCorrespondence OverheadResourceModelCorrespondence RtaOvhFpFullyNonpreemptiveCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN busy_window_recurrence_solution_correspondence". exact Logic.I. Qed.
Print Assumptions busy_window_recurrence_solution_correspondence.
Goal Logic.True. idtac "AUDIT_END busy_window_recurrence_solution_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rta_recurrence_solution_correspondence". exact Logic.I. Qed.
Print Assumptions rta_recurrence_solution_correspondence.
Goal Logic.True. idtac "AUDIT_END rta_recurrence_solution_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN uniprocessor_response_time_bound_fully_non_preemptive_fp_correspondence". exact Logic.I. Qed.
Print Assumptions uniprocessor_response_time_bound_fully_non_preemptive_fp_correspondence.
Goal Logic.True. idtac "AUDIT_END uniprocessor_response_time_bound_fully_non_preemptive_fp_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rofnp_task_cost_of_job_related". exact Logic.I. Qed.
Print Assumptions rofnp_task_cost_of_job_related.
Goal Logic.True. idtac "AUDIT_END rofnp_task_cost_of_job_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rofnp_valid_job_costs_rel". exact Logic.I. Qed.
Print Assumptions rofnp_valid_job_costs_rel.
Goal Logic.True. idtac "AUDIT_END rofnp_valid_job_costs_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rofnp_all_jobs_from_taskset_rel". exact Logic.I. Qed.
Print Assumptions rofnp_all_jobs_from_taskset_rel.
Goal Logic.True. idtac "AUDIT_END rofnp_all_jobs_from_taskset_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rofnp_valid_task_arrival_sequence_rel". exact Logic.I. Qed.
Print Assumptions rofnp_valid_task_arrival_sequence_rel.
Goal Logic.True. idtac "AUDIT_END rofnp_valid_task_arrival_sequence_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rofnp_positive_costs_rel". exact Logic.I. Qed.
Print Assumptions rofnp_positive_costs_rel.
Goal Logic.True. idtac "AUDIT_END rofnp_positive_costs_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rofnp_ovh_sched". exact Logic.I. Qed.
Print Assumptions rofnp_ovh_sched.
Goal Logic.True. idtac "AUDIT_END rofnp_ovh_sched". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rofnp_basic_ready_rel". exact Logic.I. Qed.
Print Assumptions rofnp_basic_ready_rel.
Goal Logic.True. idtac "AUDIT_END rofnp_basic_ready_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rofnp_preempted_at_related". exact Logic.I. Qed.
Print Assumptions rofnp_preempted_at_related.
Goal Logic.True. idtac "AUDIT_END rofnp_preempted_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rofnp_no_superfluous_rel". exact Logic.I. Qed.
Print Assumptions rofnp_no_superfluous_rel.
Goal Logic.True. idtac "AUDIT_END rofnp_no_superfluous_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rofnp_forall_fp". exact Logic.I. Qed.
Print Assumptions rofnp_forall_fp.
Goal Logic.True. idtac "AUDIT_END rofnp_forall_fp". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rofnp_reflexive_task_rel". exact Logic.I. Qed.
Print Assumptions rofnp_reflexive_task_rel.
Goal Logic.True. idtac "AUDIT_END rofnp_reflexive_task_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rofnp_transitive_task_rel". exact Logic.I. Qed.
Print Assumptions rofnp_transitive_task_rel.
Goal Logic.True. idtac "AUDIT_END rofnp_transitive_task_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rofnp_fp_hep_job_related". exact Logic.I. Qed.
Print Assumptions rofnp_fp_hep_job_related.
Goal Logic.True. idtac "AUDIT_END rofnp_fp_hep_job_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rofnp_same_task_related". exact Logic.I. Qed.
Print Assumptions rofnp_same_task_related.
Goal Logic.True. idtac "AUDIT_END rofnp_same_task_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rofnp_sequential_tasks_rel". exact Logic.I. Qed.
Print Assumptions rofnp_sequential_tasks_rel.
Goal Logic.True. idtac "AUDIT_END rofnp_sequential_tasks_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rofnp_task_model_related". exact Logic.I. Qed.
Print Assumptions rofnp_task_model_related.
Goal Logic.True. idtac "AUDIT_END rofnp_task_model_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rofnp_job_model_related". exact Logic.I. Qed.
Print Assumptions rofnp_job_model_related.
Goal Logic.True. idtac "AUDIT_END rofnp_job_model_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rofnp_nonpreemptive_schedule_rel". exact Logic.I. Qed.
Print Assumptions rofnp_nonpreemptive_schedule_rel.
Goal Logic.True. idtac "AUDIT_END rofnp_nonpreemptive_schedule_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rofnp_job_of_task_related". exact Logic.I. Qed.
Print Assumptions rofnp_job_of_task_related.
Goal Logic.True. idtac "AUDIT_END rofnp_job_of_task_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rofnp_sum_filter_related". exact Logic.I. Qed.
Print Assumptions rofnp_sum_filter_related.
Goal Logic.True. idtac "AUDIT_END rofnp_sum_filter_related". exact Logic.I. Qed.
