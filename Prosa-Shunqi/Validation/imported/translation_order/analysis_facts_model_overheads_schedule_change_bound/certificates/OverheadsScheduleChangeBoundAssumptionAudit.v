From FoundationCertificates Require Import
  OvhArrivalsSeqBaseAdapter OvhArrivalsSeqOperations OvhArrivalsSeqCorrespondence OvhArrivalsCorrespondence OvhJitterSvcBaseAdapter OvhJitterSvcNatBoolOperations OvhJitterSvcIntervalOperations OvhJitterSvcScheduleOperations OvhJitterSvcJobOperations OvhPreemptionParameterCorrespondence OvhPreemptionTimeCorrespondence OvhPriorityDrivenCorrespondence OvhPStateCoverHelpers OvhFactsPreemptionHelpers OvhWorkloadCorrespondence OvhPriorityInversionCorrespondence OvhExistenceHelpers OvhHepAtPtHelpers OvhTaskPreemptionParametersCorrespondence OvhBusyIntervalPiHelpers OvhStateRel OvhCurvesCorrespondence ScheduleChangeBaseAdapter ScheduleChangeStateAdapter ScheduleChangeOptionOperations ScheduleChangeIntervalOperations ScheduleChangeListOperations ScheduleChangeCorrespondence OverheadsScheduleChangeBoundCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN schedule_changes_bounded_by_total_arrivals_JLFP_correspondence". exact Logic.I. Qed.
Print Assumptions schedule_changes_bounded_by_total_arrivals_JLFP_correspondence.
Goal Logic.True. idtac "AUDIT_END schedule_changes_bounded_by_total_arrivals_JLFP_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN schedule_changes_bounded_by_total_arrivals_FP_correspondence". exact Logic.I. Qed.
Print Assumptions schedule_changes_bounded_by_total_arrivals_FP_correspondence.
Goal Logic.True. idtac "AUDIT_END schedule_changes_bounded_by_total_arrivals_FP_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN schedule_changes_bounded_by_total_arrivals_FIFO_correspondence". exact Logic.I. Qed.
Print Assumptions schedule_changes_bounded_by_total_arrivals_FIFO_correspondence.
Goal Logic.True. idtac "AUDIT_END schedule_changes_bounded_by_total_arrivals_FIFO_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN scb_eqP". exact Logic.I. Qed.
Print Assumptions scb_eqP.
Goal Logic.True. idtac "AUDIT_END scb_eqP". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN scb_decidable_unique". exact Logic.I. Qed.
Print Assumptions scb_decidable_unique.
Goal Logic.True. idtac "AUDIT_END scb_decidable_unique". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN scb_decidable_eq". exact Logic.I. Qed.
Print Assumptions scb_decidable_eq.
Goal Logic.True. idtac "AUDIT_END scb_decidable_eq". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN scb_forall_list". exact Logic.I. Qed.
Print Assumptions scb_forall_list.
Goal Logic.True. idtac "AUDIT_END scb_forall_list". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN scb_sum_filter_related". exact Logic.I. Qed.
Print Assumptions scb_sum_filter_related.
Goal Logic.True. idtac "AUDIT_END scb_sum_filter_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN scb_FP_policy_source_total". exact Logic.I. Qed.
Print Assumptions scb_FP_policy_source_total.
Goal Logic.True. idtac "AUDIT_END scb_FP_policy_source_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN scb_FP_policy_target_total". exact Logic.I. Qed.
Print Assumptions scb_FP_policy_target_total.
Goal Logic.True. idtac "AUDIT_END scb_FP_policy_target_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN scb_forall_ja". exact Logic.I. Qed.
Print Assumptions scb_forall_ja.
Goal Logic.True. idtac "AUDIT_END scb_forall_ja". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN scb_forall_cost". exact Logic.I. Qed.
Print Assumptions scb_forall_cost.
Goal Logic.True. idtac "AUDIT_END scb_forall_cost". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN scb_forall_jt". exact Logic.I. Qed.
Print Assumptions scb_forall_jt.
Goal Logic.True. idtac "AUDIT_END scb_forall_jt". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN scb_forall_task". exact Logic.I. Qed.
Print Assumptions scb_forall_task.
Goal Logic.True. idtac "AUDIT_END scb_forall_task". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN scb_sc_sched". exact Logic.I. Qed.
Print Assumptions scb_sc_sched.
Goal Logic.True. idtac "AUDIT_END scb_sc_sched". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN scb_count_related". exact Logic.I. Qed.
Print Assumptions scb_count_related.
Goal Logic.True. idtac "AUDIT_END scb_count_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN scb_basic_ready_rel". exact Logic.I. Qed.
Print Assumptions scb_basic_ready_rel.
Goal Logic.True. idtac "AUDIT_END scb_basic_ready_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN scb_preempted_at_related". exact Logic.I. Qed.
Print Assumptions scb_preempted_at_related.
Goal Logic.True. idtac "AUDIT_END scb_preempted_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN scb_no_superfluous_rel". exact Logic.I. Qed.
Print Assumptions scb_no_superfluous_rel.
Goal Logic.True. idtac "AUDIT_END scb_no_superfluous_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN scb_all_jobs_from_taskset_related". exact Logic.I. Qed.
Print Assumptions scb_all_jobs_from_taskset_related.
Goal Logic.True. idtac "AUDIT_END scb_all_jobs_from_taskset_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN scb_fp_hep_job_related". exact Logic.I. Qed.
Print Assumptions scb_fp_hep_job_related.
Goal Logic.True. idtac "AUDIT_END scb_fp_hep_job_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN scb_fp_task_pred". exact Logic.I. Qed.
Print Assumptions scb_fp_task_pred.
Goal Logic.True. idtac "AUDIT_END scb_fp_task_pred". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN scb_reflexive_task_rel". exact Logic.I. Qed.
Print Assumptions scb_reflexive_task_rel.
Goal Logic.True. idtac "AUDIT_END scb_reflexive_task_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN scb_transitive_task_rel". exact Logic.I. Qed.
Print Assumptions scb_transitive_task_rel.
Goal Logic.True. idtac "AUDIT_END scb_transitive_task_rel". exact Logic.I. Qed.
