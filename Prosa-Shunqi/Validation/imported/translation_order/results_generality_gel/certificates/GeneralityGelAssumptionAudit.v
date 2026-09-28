From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence PreemptionTimeCorrespondence PriorityDrivenCorrespondence PStateCoverHelpers FactsPreemptionHelpers NatSubCorrespondence PcoBaseAdapter PcoStaticOrder PcoDynamicOrder PriorityCoercionCorrespondence PriorityGelHelpers GeneralityGelCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN gel_generalizes_edf_correspondence". exact Logic.I. Qed.
Print Assumptions gel_generalizes_edf_correspondence.
Goal Logic.True. idtac "AUDIT_END gel_generalizes_edf_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN gel_generalizes_fifo_correspondence". exact Logic.I. Qed.
Print Assumptions gel_generalizes_fifo_correspondence.
Goal Logic.True. idtac "AUDIT_END gel_generalizes_fifo_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pp_delta_correspondence". exact Logic.I. Qed.
Print Assumptions pp_delta_correspondence.
Goal Logic.True. idtac "AUDIT_END pp_delta_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN backlogged_job_has_lower_gel_prio_correspondence". exact Logic.I. Qed.
Print Assumptions backlogged_job_has_lower_gel_prio_correspondence.
Goal Logic.True. idtac "AUDIT_END backlogged_job_has_lower_gel_prio_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN gel_conditionally_generalizes_fp_correspondence". exact Logic.I. Qed.
Print Assumptions gel_conditionally_generalizes_fp_correspondence.
Goal Logic.True. idtac "AUDIT_END gel_conditionally_generalizes_fp_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN gg_subz_pp_le". exact Logic.I. Qed.
Print Assumptions gg_subz_pp_le.
Goal Logic.True. idtac "AUDIT_END gg_subz_pp_le". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN gg_subz_pp_gt". exact Logic.I. Qed.
Print Assumptions gg_subz_pp_gt.
Goal Logic.True. idtac "AUDIT_END gg_subz_pp_gt". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN gg_subz_pn". exact Logic.I. Qed.
Print Assumptions gg_subz_pn.
Goal Logic.True. idtac "AUDIT_END gg_subz_pn". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN gg_subz_np". exact Logic.I. Qed.
Print Assumptions gg_subz_np.
Goal Logic.True. idtac "AUDIT_END gg_subz_np". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN gg_subz_nn_le". exact Logic.I. Qed.
Print Assumptions gg_subz_nn_le.
Goal Logic.True. idtac "AUDIT_END gg_subz_nn_le". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN gg_subz_nn_gt". exact Logic.I. Qed.
Print Assumptions gg_subz_nn_gt.
Goal Logic.True. idtac "AUDIT_END gg_subz_nn_gt". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN gg_sub1_related". exact Logic.I. Qed.
Print Assumptions gg_sub1_related.
Goal Logic.True. idtac "AUDIT_END gg_sub1_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN gg_add1_related". exact Logic.I. Qed.
Print Assumptions gg_add1_related.
Goal Logic.True. idtac "AUDIT_END gg_add1_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN gg_sub_canonical". exact Logic.I. Qed.
Print Assumptions gg_sub_canonical.
Goal Logic.True. idtac "AUDIT_END gg_sub_canonical". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN gg_sub_related". exact Logic.I. Qed.
Print Assumptions gg_sub_related.
Goal Logic.True. idtac "AUDIT_END gg_sub_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN gg_abs_canonical". exact Logic.I. Qed.
Print Assumptions gg_abs_canonical.
Goal Logic.True. idtac "AUDIT_END gg_abs_canonical". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN gg_abs_related". exact Logic.I. Qed.
Print Assumptions gg_abs_related.
Goal Logic.True. idtac "AUDIT_END gg_abs_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN gg_zero_related". exact Logic.I. Qed.
Print Assumptions gg_zero_related.
Goal Logic.True. idtac "AUDIT_END gg_zero_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN gg_cast_related". exact Logic.I. Qed.
Print Assumptions gg_cast_related.
Goal Logic.True. idtac "AUDIT_END gg_cast_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN gg_int_eq_correspondence". exact Logic.I. Qed.
Print Assumptions gg_int_eq_correspondence.
Goal Logic.True. idtac "AUDIT_END gg_int_eq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN gg_iff_correspondence". exact Logic.I. Qed.
Print Assumptions gg_iff_correspondence.
Goal Logic.True. idtac "AUDIT_END gg_iff_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN gg_jt". exact Logic.I. Qed.
Print Assumptions gg_jt.
Goal Logic.True. idtac "AUDIT_END gg_jt". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN gg_forall_sched". exact Logic.I. Qed.
Print Assumptions gg_forall_sched.
Goal Logic.True. idtac "AUDIT_END gg_forall_sched". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN gg_gel_rel". exact Logic.I. Qed.
Print Assumptions gg_gel_rel.
Goal Logic.True. idtac "AUDIT_END gg_gel_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN gg_same_task_related". exact Logic.I. Qed.
Print Assumptions gg_same_task_related.
Goal Logic.True. idtac "AUDIT_END gg_same_task_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN gg_pp_delta_jobs". exact Logic.I. Qed.
Print Assumptions gg_pp_delta_jobs.
Goal Logic.True. idtac "AUDIT_END gg_pp_delta_jobs". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN gg_rtb_related". exact Logic.I. Qed.
Print Assumptions gg_rtb_related.
Goal Logic.True. idtac "AUDIT_END gg_rtb_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN gg_respects_gel_rel". exact Logic.I. Qed.
Print Assumptions gg_respects_gel_rel.
Goal Logic.True. idtac "AUDIT_END gg_respects_gel_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN gg_valid_schedule_rel". exact Logic.I. Qed.
Print Assumptions gg_valid_schedule_rel.
Goal Logic.True. idtac "AUDIT_END gg_valid_schedule_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN gg_sequential_tasks_rel". exact Logic.I. Qed.
Print Assumptions gg_sequential_tasks_rel.
Goal Logic.True. idtac "AUDIT_END gg_sequential_tasks_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN gg_deadline_related". exact Logic.I. Qed.
Print Assumptions gg_deadline_related.
Goal Logic.True. idtac "AUDIT_END gg_deadline_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN gg_hep_task_jobs". exact Logic.I. Qed.
Print Assumptions gg_hep_task_jobs.
Goal Logic.True. idtac "AUDIT_END gg_hep_task_jobs". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN gg_hp_task_jobs". exact Logic.I. Qed.
Print Assumptions gg_hp_task_jobs.
Goal Logic.True. idtac "AUDIT_END gg_hp_task_jobs". exact Logic.I. Qed.
