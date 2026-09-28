From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence PreemptionTimeCorrespondence PriorityDrivenCorrespondence PStateCoverHelpers FactsPreemptionHelpers ArrivalsCorrespondence CurvesCorrespondence DelayPropagationCorrespondence JitterCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN jitter_arrives_in_iff_correspondence". exact Logic.I. Qed.
Print Assumptions jitter_arrives_in_iff_correspondence.
Goal Logic.True. idtac "AUDIT_END jitter_arrives_in_iff_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN valid_release_sequence_correspondence". exact Logic.I. Qed.
Print Assumptions valid_release_sequence_correspondence.
Goal Logic.True. idtac "AUDIT_END valid_release_sequence_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN valid_release_curve_correspondence". exact Logic.I. Qed.
Print Assumptions valid_release_curve_correspondence.
Goal Logic.True. idtac "AUDIT_END valid_release_curve_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN release_curve_respected_correspondence". exact Logic.I. Qed.
Print Assumptions release_curve_respected_correspondence.
Goal Logic.True. idtac "AUDIT_END release_curve_respected_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jitter_prop_same_jobs_correspondence". exact Logic.I. Qed.
Print Assumptions jitter_prop_same_jobs_correspondence.
Goal Logic.True. idtac "AUDIT_END jitter_prop_same_jobs_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jitter_prop_same_jobs'_correspondence". exact Logic.I. Qed.
Print Assumptions jitter_prop_same_jobs'_correspondence.
Goal Logic.True. idtac "AUDIT_END jitter_prop_same_jobs'_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jitter_prop_valid_costs_correspondence". exact Logic.I. Qed.
Print Assumptions jitter_prop_valid_costs_correspondence.
Goal Logic.True. idtac "AUDIT_END jitter_prop_valid_costs_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jitter_ready_to_execute_correspondence". exact Logic.I. Qed.
Print Assumptions jitter_ready_to_execute_correspondence.
Goal Logic.True. idtac "AUDIT_END jitter_ready_to_execute_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jitter_work_conservation_correspondence". exact Logic.I. Qed.
Print Assumptions jitter_work_conservation_correspondence.
Goal Logic.True. idtac "AUDIT_END jitter_work_conservation_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jitter_valid_schedule_correspondence". exact Logic.I. Qed.
Print Assumptions jitter_valid_schedule_correspondence.
Goal Logic.True. idtac "AUDIT_END jitter_valid_schedule_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jitter_scheduled_jobs_at_equiv_correspondence". exact Logic.I. Qed.
Print Assumptions jitter_scheduled_jobs_at_equiv_correspondence.
Goal Logic.True. idtac "AUDIT_END jitter_scheduled_jobs_at_equiv_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jitter_scheduled_job_at_eq_correspondence". exact Logic.I. Qed.
Print Assumptions jitter_scheduled_job_at_eq_correspondence.
Goal Logic.True. idtac "AUDIT_END jitter_scheduled_job_at_eq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jitter_FP_compliance_correspondence". exact Logic.I. Qed.
Print Assumptions jitter_FP_compliance_correspondence.
Goal Logic.True. idtac "AUDIT_END jitter_FP_compliance_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jitter_response_time_bound_correspondence". exact Logic.I. Qed.
Print Assumptions jitter_response_time_bound_correspondence.
Goal Logic.True. idtac "AUDIT_END jitter_response_time_bound_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jit_exists_identity". exact Logic.I. Qed.
Print Assumptions jit_exists_identity.
Goal Logic.True. idtac "AUDIT_END jit_exists_identity". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jit_ohead_related". exact Logic.I. Qed.
Print Assumptions jit_ohead_related.
Goal Logic.True. idtac "AUDIT_END jit_ohead_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jit_opt_eq_correspondence". exact Logic.I. Qed.
Print Assumptions jit_opt_eq_correspondence.
Goal Logic.True. idtac "AUDIT_END jit_opt_eq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jit_release_rel". exact Logic.I. Qed.
Print Assumptions jit_release_rel.
Goal Logic.True. idtac "AUDIT_END jit_release_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jit_release_sequence_rel". exact Logic.I. Qed.
Print Assumptions jit_release_sequence_rel.
Goal Logic.True. idtac "AUDIT_END jit_release_sequence_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jit_release_curve_rel". exact Logic.I. Qed.
Print Assumptions jit_release_curve_rel.
Goal Logic.True. idtac "AUDIT_END jit_release_curve_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jit_job_task_eq_rel". exact Logic.I. Qed.
Print Assumptions jit_job_task_eq_rel.
Goal Logic.True. idtac "AUDIT_END jit_job_task_eq_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jit_valid_jitter_bounds_rel". exact Logic.I. Qed.
Print Assumptions jit_valid_jitter_bounds_rel.
Goal Logic.True. idtac "AUDIT_END jit_valid_jitter_bounds_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jit_task_mem_related". exact Logic.I. Qed.
Print Assumptions jit_task_mem_related.
Goal Logic.True. idtac "AUDIT_END jit_task_mem_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jit_all_jobs_from_taskset_rel". exact Logic.I. Qed.
Print Assumptions jit_all_jobs_from_taskset_rel.
Goal Logic.True. idtac "AUDIT_END jit_all_jobs_from_taskset_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jit_job_of_task_related". exact Logic.I. Qed.
Print Assumptions jit_job_of_task_related.
Goal Logic.True. idtac "AUDIT_END jit_job_of_task_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jit_forall_task_cost". exact Logic.I. Qed.
Print Assumptions jit_forall_task_cost.
Goal Logic.True. idtac "AUDIT_END jit_forall_task_cost". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jit_forall_job_cost". exact Logic.I. Qed.
Print Assumptions jit_forall_job_cost.
Goal Logic.True. idtac "AUDIT_END jit_forall_job_cost". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jit_valid_job_costs_rel". exact Logic.I. Qed.
Print Assumptions jit_valid_job_costs_rel.
Goal Logic.True. idtac "AUDIT_END jit_valid_job_costs_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jit_forall_fp". exact Logic.I. Qed.
Print Assumptions jit_forall_fp.
Goal Logic.True. idtac "AUDIT_END jit_forall_fp". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jit_forall_list". exact Logic.I. Qed.
Print Assumptions jit_forall_list.
Goal Logic.True. idtac "AUDIT_END jit_forall_list". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jit_jitter_ready_rel". exact Logic.I. Qed.
Print Assumptions jit_jitter_ready_rel.
Goal Logic.True. idtac "AUDIT_END jit_jitter_ready_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jit_basic_ready_rel". exact Logic.I. Qed.
Print Assumptions jit_basic_ready_rel.
Goal Logic.True. idtac "AUDIT_END jit_basic_ready_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jit_must_be_ready_rel". exact Logic.I. Qed.
Print Assumptions jit_must_be_ready_rel.
Goal Logic.True. idtac "AUDIT_END jit_must_be_ready_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jit_backlogged_related". exact Logic.I. Qed.
Print Assumptions jit_backlogged_related.
Goal Logic.True. idtac "AUDIT_END jit_backlogged_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jit_valid_schedule_rel". exact Logic.I. Qed.
Print Assumptions jit_valid_schedule_rel.
Goal Logic.True. idtac "AUDIT_END jit_valid_schedule_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jit_work_conserving_rel". exact Logic.I. Qed.
Print Assumptions jit_work_conserving_rel.
Goal Logic.True. idtac "AUDIT_END jit_work_conserving_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jit_respects_fp_rel". exact Logic.I. Qed.
Print Assumptions jit_respects_fp_rel.
Goal Logic.True. idtac "AUDIT_END jit_respects_fp_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jit_scheduled_jobs_at_related". exact Logic.I. Qed.
Print Assumptions jit_scheduled_jobs_at_related.
Goal Logic.True. idtac "AUDIT_END jit_scheduled_jobs_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jit_scheduled_job_at_related". exact Logic.I. Qed.
Print Assumptions jit_scheduled_job_at_related.
Goal Logic.True. idtac "AUDIT_END jit_scheduled_job_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jit_response_time_bound_rel". exact Logic.I. Qed.
Print Assumptions jit_response_time_bound_rel.
Goal Logic.True. idtac "AUDIT_END jit_response_time_bound_rel". exact Logic.I. Qed.
