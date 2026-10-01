From FoundationCertificates Require Import
  PmArrivalsSeqBaseAdapter PmArrivalsSeqOperations PmArrivalsSeqCorrespondence PmJitterSvcBaseAdapter PmJitterSvcNatBoolOperations PmJitterSvcIntervalOperations PmJitterSvcScheduleOperations PmJitterSvcJobOperations PmCriterionDefs PmFinishTimeMinBridge PaperModelCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN JobPredecessors_source_total". exact Logic.I. Qed.
Print Assumptions JobPredecessors_source_total.
Goal Logic.True. idtac "AUDIT_END JobPredecessors_source_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN JobPredecessors_target_total". exact Logic.I. Qed.
Print Assumptions JobPredecessors_target_total.
Goal Logic.True. idtac "AUDIT_END JobPredecessors_target_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN JobDelay_source_total". exact Logic.I. Qed.
Print Assumptions JobDelay_source_total.
Goal Logic.True. idtac "AUDIT_END JobDelay_source_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN JobDelay_target_total". exact Logic.I. Qed.
Print Assumptions JobDelay_target_total.
Goal Logic.True. idtac "AUDIT_END JobDelay_target_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN SystemEvolutions_source_total". exact Logic.I. Qed.
Print Assumptions SystemEvolutions_source_total.
Goal Logic.True. idtac "AUDIT_END SystemEvolutions_source_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN SystemEvolutions_target_total". exact Logic.I. Qed.
Print Assumptions SystemEvolutions_target_total.
Goal Logic.True. idtac "AUDIT_END SystemEvolutions_target_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Scheduler_source_total". exact Logic.I. Qed.
Print Assumptions Scheduler_source_total.
Goal Logic.True. idtac "AUDIT_END Scheduler_source_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Scheduler_target_total". exact Logic.I. Qed.
Print Assumptions Scheduler_target_total.
Goal Logic.True. idtac "AUDIT_END Scheduler_target_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Scheduler_generic_source_total". exact Logic.I. Qed.
Print Assumptions Scheduler_generic_source_total.
Goal Logic.True. idtac "AUDIT_END Scheduler_generic_source_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Scheduler_generic_target_total". exact Logic.I. Qed.
Print Assumptions Scheduler_generic_target_total.
Goal Logic.True. idtac "AUDIT_END Scheduler_generic_target_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN schedulability_transferred_AB_correspondence". exact Logic.I. Qed.
Print Assumptions schedulability_transferred_AB_correspondence.
Goal Logic.True. idtac "AUDIT_END schedulability_transferred_AB_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN clairvoyant_criterion_correspondence". exact Logic.I. Qed.
Print Assumptions clairvoyant_criterion_correspondence.
Goal Logic.True. idtac "AUDIT_END clairvoyant_criterion_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN clairvoyant_sufficiency_correspondence". exact Logic.I. Qed.
Print Assumptions clairvoyant_sufficiency_correspondence.
Goal Logic.True. idtac "AUDIT_END clairvoyant_sufficiency_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN clairvoyant_necessity_correspondence". exact Logic.I. Qed.
Print Assumptions clairvoyant_necessity_correspondence.
Goal Logic.True. idtac "AUDIT_END clairvoyant_necessity_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN nonclairvoyant_criterion_correspondence". exact Logic.I. Qed.
Print Assumptions nonclairvoyant_criterion_correspondence.
Goal Logic.True. idtac "AUDIT_END nonclairvoyant_criterion_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN nonclairvoyant_sufficiency_correspondence". exact Logic.I. Qed.
Print Assumptions nonclairvoyant_sufficiency_correspondence.
Goal Logic.True. idtac "AUDIT_END nonclairvoyant_sufficiency_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ref_finish_time_correspondence". exact Logic.I. Qed.
Print Assumptions ref_finish_time_correspondence.
Goal Logic.True. idtac "AUDIT_END ref_finish_time_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN online_response_time_bound_correspondence". exact Logic.I. Qed.
Print Assumptions online_response_time_bound_correspondence.
Goal Logic.True. idtac "AUDIT_END online_response_time_bound_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN online_finish_time_correspondence". exact Logic.I. Qed.
Print Assumptions online_finish_time_correspondence.
Goal Logic.True. idtac "AUDIT_END online_finish_time_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN online_finish_time_bounded_correspondence". exact Logic.I. Qed.
Print Assumptions online_finish_time_bounded_correspondence.
Goal Logic.True. idtac "AUDIT_END online_finish_time_bounded_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN clairvoyant_sufficiency'_correspondence". exact Logic.I. Qed.
Print Assumptions clairvoyant_sufficiency'_correspondence.
Goal Logic.True. idtac "AUDIT_END clairvoyant_sufficiency'_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN nonclairvoyant_sufficiency'_correspondence". exact Logic.I. Qed.
Print Assumptions nonclairvoyant_sufficiency'_correspondence.
Goal Logic.True. idtac "AUDIT_END nonclairvoyant_sufficiency'_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN online_finish_time'_correspondence". exact Logic.I. Qed.
Print Assumptions online_finish_time'_correspondence.
Goal Logic.True. idtac "AUDIT_END online_finish_time'_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN online_finish_time_bounded'_correspondence". exact Logic.I. Qed.
Print Assumptions online_finish_time_bounded'_correspondence.
Goal Logic.True. idtac "AUDIT_END online_finish_time_bounded'_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN clairvoyant_necessity'_correspondence". exact Logic.I. Qed.
Print Assumptions clairvoyant_necessity'_correspondence.
Goal Logic.True. idtac "AUDIT_END clairvoyant_necessity'_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pm_forall_type". exact Logic.I. Qed.
Print Assumptions pm_forall_type.
Goal Logic.True. idtac "AUDIT_END pm_forall_type". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pm_forall_proof". exact Logic.I. Qed.
Print Assumptions pm_forall_proof.
Goal Logic.True. idtac "AUDIT_END pm_forall_proof". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pm_forall_pred". exact Logic.I. Qed.
Print Assumptions pm_forall_pred.
Goal Logic.True. idtac "AUDIT_END pm_forall_pred". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pm_forall_evo". exact Logic.I. Qed.
Print Assumptions pm_forall_evo.
Goal Logic.True. idtac "AUDIT_END pm_forall_evo". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pm_all_canonical". exact Logic.I. Qed.
Print Assumptions pm_all_canonical.
Goal Logic.True. idtac "AUDIT_END pm_all_canonical". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pm_all_related". exact Logic.I. Qed.
Print Assumptions pm_all_related.
Goal Logic.True. idtac "AUDIT_END pm_all_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pm_job_ready_related". exact Logic.I. Qed.
Print Assumptions pm_job_ready_related.
Goal Logic.True. idtac "AUDIT_END pm_job_ready_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pm_valid_schedule_rel". exact Logic.I. Qed.
Print Assumptions pm_valid_schedule_rel.
Goal Logic.True. idtac "AUDIT_END pm_valid_schedule_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pm_jrtb_related". exact Logic.I. Qed.
Print Assumptions pm_jrtb_related.
Goal Logic.True. idtac "AUDIT_END pm_jrtb_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pm_finish_time_rel". exact Logic.I. Qed.
Print Assumptions pm_finish_time_rel.
Goal Logic.True. idtac "AUDIT_END pm_finish_time_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pm_forall_alg". exact Logic.I. Qed.
Print Assumptions pm_forall_alg.
Goal Logic.True. idtac "AUDIT_END pm_forall_alg". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pm_bound_source_total". exact Logic.I. Qed.
Print Assumptions pm_bound_source_total.
Goal Logic.True. idtac "AUDIT_END pm_bound_source_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pm_bound_target_total". exact Logic.I. Qed.
Print Assumptions pm_bound_target_total.
Goal Logic.True. idtac "AUDIT_END pm_bound_target_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pm_ns_target_total". exact Logic.I. Qed.
Print Assumptions pm_ns_target_total.
Goal Logic.True. idtac "AUDIT_END pm_ns_target_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pm_ns_pick_at". exact Logic.I. Qed.
Print Assumptions pm_ns_pick_at.
Goal Logic.True. idtac "AUDIT_END pm_ns_pick_at". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pm_ns_to_target_at_jf". exact Logic.I. Qed.
Print Assumptions pm_ns_to_target_at_jf.
Goal Logic.True. idtac "AUDIT_END pm_ns_to_target_at_jf". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pm_max_cost_rel". exact Logic.I. Qed.
Print Assumptions pm_max_cost_rel.
Goal Logic.True. idtac "AUDIT_END pm_max_cost_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pm_vs". exact Logic.I. Qed.
Print Assumptions pm_vs.
Goal Logic.True. idtac "AUDIT_END pm_vs". exact Logic.I. Qed.
