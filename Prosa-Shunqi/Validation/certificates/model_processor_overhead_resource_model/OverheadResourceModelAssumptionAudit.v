From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ScheduleChangeBaseAdapter ScheduleChangeStateAdapter ScheduleChangeOptionOperations ScheduleChangeIntervalOperations ScheduleChangeListOperations ScheduleChangeCorrespondence OverheadsBaseAdapter OverheadsNatBoolOperations OverheadsIntervalOperations OverheadsCorrespondence OverheadResourceModelCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN time_spent_in_dispatch_correspondence". exact Logic.I. Qed.
Print Assumptions time_spent_in_dispatch_correspondence.
Goal Logic.True. idtac "AUDIT_END time_spent_in_dispatch_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN time_spent_in_context_switch_correspondence". exact Logic.I. Qed.
Print Assumptions time_spent_in_context_switch_correspondence.
Goal Logic.True. idtac "AUDIT_END time_spent_in_context_switch_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN time_spent_in_CRPD_correspondence". exact Logic.I. Qed.
Print Assumptions time_spent_in_CRPD_correspondence.
Goal Logic.True. idtac "AUDIT_END time_spent_in_CRPD_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN time_spent_in_dispatch_is_bounded_by_correspondence". exact Logic.I. Qed.
Print Assumptions time_spent_in_dispatch_is_bounded_by_correspondence.
Goal Logic.True. idtac "AUDIT_END time_spent_in_dispatch_is_bounded_by_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN time_spent_in_context_switch_is_bounded_by_correspondence". exact Logic.I. Qed.
Print Assumptions time_spent_in_context_switch_is_bounded_by_correspondence.
Goal Logic.True. idtac "AUDIT_END time_spent_in_context_switch_is_bounded_by_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN time_spent_in_CRPD_is_bounded_by_correspondence". exact Logic.I. Qed.
Print Assumptions time_spent_in_CRPD_is_bounded_by_correspondence.
Goal Logic.True. idtac "AUDIT_END time_spent_in_CRPD_is_bounded_by_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN dispatch_precedes_context_switch_correspondence". exact Logic.I. Qed.
Print Assumptions dispatch_precedes_context_switch_correspondence.
Goal Logic.True. idtac "AUDIT_END dispatch_precedes_context_switch_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN context_switch_precedes_progress_correspondence". exact Logic.I. Qed.
Print Assumptions context_switch_precedes_progress_correspondence.
Goal Logic.True. idtac "AUDIT_END context_switch_precedes_progress_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN context_switch_precedes_CRPD_correspondence". exact Logic.I. Qed.
Print Assumptions context_switch_precedes_CRPD_correspondence.
Goal Logic.True. idtac "AUDIT_END context_switch_precedes_CRPD_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN overhead_resource_model_correspondence". exact Logic.I. Qed.
Print Assumptions overhead_resource_model_correspondence.
Goal Logic.True. idtac "AUDIT_END overhead_resource_model_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN orm_opt_from_rel". exact Logic.I. Qed.
Print Assumptions orm_opt_from_rel.
Goal Logic.True. idtac "AUDIT_END orm_opt_from_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN orm_forall_option". exact Logic.I. Qed.
Print Assumptions orm_forall_option.
Goal Logic.True. idtac "AUDIT_END orm_forall_option". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN orm_negb_related". exact Logic.I. Qed.
Print Assumptions orm_negb_related.
Goal Logic.True. idtac "AUDIT_END orm_negb_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN orm_sc_ar". exact Logic.I. Qed.
Print Assumptions orm_sc_ar.
Goal Logic.True. idtac "AUDIT_END orm_sc_ar". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN orm_ovh_ar". exact Logic.I. Qed.
Print Assumptions orm_ovh_ar.
Goal Logic.True. idtac "AUDIT_END orm_ovh_ar". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN orm_state_maps_agree". exact Logic.I. Qed.
Print Assumptions orm_state_maps_agree.
Goal Logic.True. idtac "AUDIT_END orm_state_maps_agree". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN orm_sc_sched". exact Logic.I. Qed.
Print Assumptions orm_sc_sched.
Goal Logic.True. idtac "AUDIT_END orm_sc_sched". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN orm_job_is_related". exact Logic.I. Qed.
Print Assumptions orm_job_is_related.
Goal Logic.True. idtac "AUDIT_END orm_job_is_related". exact Logic.I. Qed.
