From FoundationCertificates Require Import
  ExcArrivalsSeqBaseAdapter ExcArrivalsSeqOperations ExcArrivalsSeqCorrespondence ExcArrivalsCorrespondence ExcJitterSvcBaseAdapter ExcJitterSvcNatBoolOperations ExcJitterSvcIntervalOperations ExcJitterSvcScheduleOperations ExcJitterSvcJobOperations ExcPreemptionParameterCorrespondence ExcPreemptionTimeCorrespondence ExcPriorityDrivenCorrespondence ExcPStateCoverHelpers ExcFactsPreemptionHelpers ExcWorkloadCorrespondence ExcPriorityInversionCorrespondence ExcExistenceHelpers ExcHepAtPtHelpers ExcTaskPreemptionParametersCorrespondence ExcBusyIntervalPiHelpers ExcStateRel ExcCurvesCorrespondence ExcRequestBoundFunctionCorrespondence ExcBlockingBoundFpCorrespondence ExcSearchSpaceFpCorrespondence RtaExcFpFullyNonpreemptiveCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN busy_window_recurrence_solution_correspondence". exact Logic.I. Qed.
Print Assumptions busy_window_recurrence_solution_correspondence.
Goal Logic.True. idtac "AUDIT_END busy_window_recurrence_solution_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rta_recurrence_solution_correspondence". exact Logic.I. Qed.
Print Assumptions rta_recurrence_solution_correspondence.
Goal Logic.True. idtac "AUDIT_END rta_recurrence_solution_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN uniprocessor_response_time_bound_fully_nonpreemptive_fp_correspondence". exact Logic.I. Qed.
Print Assumptions uniprocessor_response_time_bound_fully_nonpreemptive_fp_correspondence.
Goal Logic.True. idtac "AUDIT_END uniprocessor_response_time_bound_fully_nonpreemptive_fp_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rexc_all_canonical". exact Logic.I. Qed.
Print Assumptions rexc_all_canonical.
Goal Logic.True. idtac "AUDIT_END rexc_all_canonical". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rexc_all_related". exact Logic.I. Qed.
Print Assumptions rexc_all_related.
Goal Logic.True. idtac "AUDIT_END rexc_all_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rexc_task_cost_of_job_related". exact Logic.I. Qed.
Print Assumptions rexc_task_cost_of_job_related.
Goal Logic.True. idtac "AUDIT_END rexc_task_cost_of_job_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rexc_valid_job_costs_rel". exact Logic.I. Qed.
Print Assumptions rexc_valid_job_costs_rel.
Goal Logic.True. idtac "AUDIT_END rexc_valid_job_costs_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rexc_all_jobs_from_taskset_rel". exact Logic.I. Qed.
Print Assumptions rexc_all_jobs_from_taskset_rel.
Goal Logic.True. idtac "AUDIT_END rexc_all_jobs_from_taskset_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rexc_valid_task_arrival_sequence_rel". exact Logic.I. Qed.
Print Assumptions rexc_valid_task_arrival_sequence_rel.
Goal Logic.True. idtac "AUDIT_END rexc_valid_task_arrival_sequence_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rexc_positive_costs_rel". exact Logic.I. Qed.
Print Assumptions rexc_positive_costs_rel.
Goal Logic.True. idtac "AUDIT_END rexc_positive_costs_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rexc_prior_jobs_complete_related". exact Logic.I. Qed.
Print Assumptions rexc_prior_jobs_complete_related.
Goal Logic.True. idtac "AUDIT_END rexc_prior_jobs_complete_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rexc_sequential_ready_rel". exact Logic.I. Qed.
Print Assumptions rexc_sequential_ready_rel.
Goal Logic.True. idtac "AUDIT_END rexc_sequential_ready_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rexc_is_exceedance_exec_related". exact Logic.I. Qed.
Print Assumptions rexc_is_exceedance_exec_related.
Goal Logic.True. idtac "AUDIT_END rexc_is_exceedance_exec_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rexc_forall_fp". exact Logic.I. Qed.
Print Assumptions rexc_forall_fp.
Goal Logic.True. idtac "AUDIT_END rexc_forall_fp". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rexc_reflexive_task_rel". exact Logic.I. Qed.
Print Assumptions rexc_reflexive_task_rel.
Goal Logic.True. idtac "AUDIT_END rexc_reflexive_task_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rexc_transitive_task_rel". exact Logic.I. Qed.
Print Assumptions rexc_transitive_task_rel.
Goal Logic.True. idtac "AUDIT_END rexc_transitive_task_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rexc_fp_hep_job_related". exact Logic.I. Qed.
Print Assumptions rexc_fp_hep_job_related.
Goal Logic.True. idtac "AUDIT_END rexc_fp_hep_job_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rexc_task_model_related". exact Logic.I. Qed.
Print Assumptions rexc_task_model_related.
Goal Logic.True. idtac "AUDIT_END rexc_task_model_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rexc_job_model_related". exact Logic.I. Qed.
Print Assumptions rexc_job_model_related.
Goal Logic.True. idtac "AUDIT_END rexc_job_model_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rexc_nonpreemptive_schedule_rel". exact Logic.I. Qed.
Print Assumptions rexc_nonpreemptive_schedule_rel.
Goal Logic.True. idtac "AUDIT_END rexc_nonpreemptive_schedule_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rexc_job_of_task_related". exact Logic.I. Qed.
Print Assumptions rexc_job_of_task_related.
Goal Logic.True. idtac "AUDIT_END rexc_job_of_task_related". exact Logic.I. Qed.
