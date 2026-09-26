From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence IdealUniSchedulerCorrespondence PreemptionAwareCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN allocation_at_idle_correspondence". exact Logic.I. Qed.
Print Assumptions allocation_at_idle_correspondence.
Goal Logic.True. idtac "AUDIT_END allocation_at_idle_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN idle_schedule_no_backlogged_jobs_correspondence". exact Logic.I. Qed.
Print Assumptions idle_schedule_no_backlogged_jobs_correspondence.
Goal Logic.True. idtac "AUDIT_END idle_schedule_no_backlogged_jobs_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN np_schedule_work_conserving_correspondence". exact Logic.I. Qed.
Print Assumptions np_schedule_work_conserving_correspondence.
Goal Logic.True. idtac "AUDIT_END np_schedule_work_conserving_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN np_schedule_jobs_from_arrival_sequence_correspondence". exact Logic.I. Qed.
Print Assumptions np_schedule_jobs_from_arrival_sequence_correspondence.
Goal Logic.True. idtac "AUDIT_END np_schedule_jobs_from_arrival_sequence_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN chosen_job_is_ready_correspondence". exact Logic.I. Qed.
Print Assumptions chosen_job_is_ready_correspondence.
Goal Logic.True. idtac "AUDIT_END chosen_job_is_ready_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jobs_must_be_ready_correspondence". exact Logic.I. Qed.
Print Assumptions jobs_must_be_ready_correspondence.
Goal Logic.True. idtac "AUDIT_END jobs_must_be_ready_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN np_schedule_valid_correspondence". exact Logic.I. Qed.
Print Assumptions np_schedule_valid_correspondence.
Goal Logic.True. idtac "AUDIT_END np_schedule_valid_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN np_job_remains_scheduled_correspondence". exact Logic.I. Qed.
Print Assumptions np_job_remains_scheduled_correspondence.
Goal Logic.True. idtac "AUDIT_END np_job_remains_scheduled_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN np_consistent_correspondence". exact Logic.I. Qed.
Print Assumptions np_consistent_correspondence.
Goal Logic.True. idtac "AUDIT_END np_consistent_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN np_respects_preemption_model_correspondence". exact Logic.I. Qed.
Print Assumptions np_respects_preemption_model_correspondence.
Goal Logic.True. idtac "AUDIT_END np_respects_preemption_model_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pa_forall_cover". exact Logic.I. Qed.
Print Assumptions pa_forall_cover.
Goal Logic.True. idtac "AUDIT_END pa_forall_cover". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pa_forall_cond_cover". exact Logic.I. Qed.
Print Assumptions pa_forall_cond_cover.
Goal Logic.True. idtac "AUDIT_END pa_forall_cond_cover". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pa_exists_identity_correspondence". exact Logic.I. Qed.
Print Assumptions pa_exists_identity_correspondence.
Goal Logic.True. idtac "AUDIT_END pa_exists_identity_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pa_bool_eq_correspondence". exact Logic.I. Qed.
Print Assumptions pa_bool_eq_correspondence.
Goal Logic.True. idtac "AUDIT_END pa_bool_eq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pa_bool_true_elim". exact Logic.I. Qed.
Print Assumptions pa_bool_true_elim.
Goal Logic.True. idtac "AUDIT_END pa_bool_true_elim". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pa_true_of_rocq". exact Logic.I. Qed.
Print Assumptions pa_true_of_rocq.
Goal Logic.True. idtac "AUDIT_END pa_true_of_rocq". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pa_list_input". exact Logic.I. Qed.
Print Assumptions pa_list_input.
Goal Logic.True. idtac "AUDIT_END pa_list_input". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pa_forall_list". exact Logic.I. Qed.
Print Assumptions pa_forall_list.
Goal Logic.True. idtac "AUDIT_END pa_forall_list". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pa_sched_to_target_rel". exact Logic.I. Qed.
Print Assumptions pa_sched_to_target_rel.
Goal Logic.True. idtac "AUDIT_END pa_sched_to_target_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pa_sched_to_source_rel". exact Logic.I. Qed.
Print Assumptions pa_sched_to_source_rel.
Goal Logic.True. idtac "AUDIT_END pa_sched_to_source_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pa_forall_sched". exact Logic.I. Qed.
Print Assumptions pa_forall_sched.
Goal Logic.True. idtac "AUDIT_END pa_forall_sched". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pa_pointwise". exact Logic.I. Qed.
Print Assumptions pa_pointwise.
Goal Logic.True. idtac "AUDIT_END pa_pointwise". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pa_ideal_is_idle_related". exact Logic.I. Qed.
Print Assumptions pa_ideal_is_idle_related.
Goal Logic.True. idtac "AUDIT_END pa_ideal_is_idle_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pa_identical_prefix_rel". exact Logic.I. Qed.
Print Assumptions pa_identical_prefix_rel.
Goal Logic.True. idtac "AUDIT_END pa_identical_prefix_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pa_pending_related". exact Logic.I. Qed.
Print Assumptions pa_pending_related.
Goal Logic.True. idtac "AUDIT_END pa_pending_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pa_ready_to_target_rel". exact Logic.I. Qed.
Print Assumptions pa_ready_to_target_rel.
Goal Logic.True. idtac "AUDIT_END pa_ready_to_target_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pa_ready_to_source_rel". exact Logic.I. Qed.
Print Assumptions pa_ready_to_source_rel.
Goal Logic.True. idtac "AUDIT_END pa_ready_to_source_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pa_nonclair_rel". exact Logic.I. Qed.
Print Assumptions pa_nonclair_rel.
Goal Logic.True. idtac "AUDIT_END pa_nonclair_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pa_forall_nonclair_ready". exact Logic.I. Qed.
Print Assumptions pa_forall_nonclair_ready.
Goal Logic.True. idtac "AUDIT_END pa_forall_nonclair_ready". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pa_forall_preemptable". exact Logic.I. Qed.
Print Assumptions pa_forall_preemptable.
Goal Logic.True. idtac "AUDIT_END pa_forall_preemptable". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pa_choose_to_target_rel". exact Logic.I. Qed.
Print Assumptions pa_choose_to_target_rel.
Goal Logic.True. idtac "AUDIT_END pa_choose_to_target_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pa_choose_to_source_rel". exact Logic.I. Qed.
Print Assumptions pa_choose_to_source_rel.
Goal Logic.True. idtac "AUDIT_END pa_choose_to_source_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pa_forall_choose". exact Logic.I. Qed.
Print Assumptions pa_forall_choose.
Goal Logic.True. idtac "AUDIT_END pa_forall_choose". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pa_non_idling_rel". exact Logic.I. Qed.
Print Assumptions pa_non_idling_rel.
Goal Logic.True. idtac "AUDIT_END pa_non_idling_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pa_chooses_from_rel". exact Logic.I. Qed.
Print Assumptions pa_chooses_from_rel.
Goal Logic.True. idtac "AUDIT_END pa_chooses_from_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pa_pmc_related". exact Logic.I. Qed.
Print Assumptions pa_pmc_related.
Goal Logic.True. idtac "AUDIT_END pa_pmc_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pa_alloc_related". exact Logic.I. Qed.
Print Assumptions pa_alloc_related.
Goal Logic.True. idtac "AUDIT_END pa_alloc_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pa_sut_related". exact Logic.I. Qed.
Print Assumptions pa_sut_related.
Goal Logic.True. idtac "AUDIT_END pa_sut_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pa_preemption_time_related". exact Logic.I. Qed.
Print Assumptions pa_preemption_time_related.
Goal Logic.True. idtac "AUDIT_END pa_preemption_time_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pa_jobs_come_from_rel". exact Logic.I. Qed.
Print Assumptions pa_jobs_come_from_rel.
Goal Logic.True. idtac "AUDIT_END pa_jobs_come_from_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pa_must_be_ready_rel". exact Logic.I. Qed.
Print Assumptions pa_must_be_ready_rel.
Goal Logic.True. idtac "AUDIT_END pa_must_be_ready_rel". exact Logic.I. Qed.
