From FoundationCertificates Require Import
  OvhArrivalsSeqBaseAdapter OvhArrivalsSeqOperations OvhArrivalsSeqCorrespondence OvhArrivalsCorrespondence OvhJitterSvcBaseAdapter OvhJitterSvcNatBoolOperations OvhJitterSvcIntervalOperations OvhJitterSvcScheduleOperations OvhJitterSvcJobOperations OvhPreemptionParameterCorrespondence OvhPreemptionTimeCorrespondence OvhPriorityDrivenCorrespondence OvhPStateCoverHelpers OvhFactsPreemptionHelpers OvhWorkloadCorrespondence OvhPriorityInversionCorrespondence OvhExistenceHelpers OvhHepAtPtHelpers OvhTaskPreemptionParametersCorrespondence OvhBusyIntervalPiHelpers OvhStateRel ScheduleChangeBaseAdapter ScheduleChangeStateAdapter ScheduleChangeOptionOperations ScheduleChangeIntervalOperations ScheduleChangeListOperations ScheduleChangeCorrespondence ArrivalsSeqBaseAdapter ArrivalsSeqOperations OverheadsBaseAdapter OverheadsNatBoolOperations OverheadsIntervalOperations OverheadsCorrespondence OverheadResourceModelCorrespondence OverheadsBlackoutBoundCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN blackout_during_split_correspondence". exact Logic.I. Qed.
Print Assumptions blackout_during_split_correspondence.
Goal Logic.True. idtac "AUDIT_END blackout_during_split_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN total_dispatch_time_eq_job_dispatch_time_correspondence". exact Logic.I. Qed.
Print Assumptions total_dispatch_time_eq_job_dispatch_time_correspondence.
Goal Logic.True. idtac "AUDIT_END total_dispatch_time_eq_job_dispatch_time_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN total_cswitch_time_eq_job_cswitch_time_correspondence". exact Logic.I. Qed.
Print Assumptions total_cswitch_time_eq_job_cswitch_time_correspondence.
Goal Logic.True. idtac "AUDIT_END total_cswitch_time_eq_job_cswitch_time_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN total_CRPD_time_eq_job_CRPD_time_correspondence". exact Logic.I. Qed.
Print Assumptions total_CRPD_time_eq_job_CRPD_time_correspondence.
Goal Logic.True. idtac "AUDIT_END total_CRPD_time_eq_job_CRPD_time_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN total_time_in_dispatch_is_bounded_correspondence". exact Logic.I. Qed.
Print Assumptions total_time_in_dispatch_is_bounded_correspondence.
Goal Logic.True. idtac "AUDIT_END total_time_in_dispatch_is_bounded_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN total_time_in_cswitch_is_bounded_correspondence". exact Logic.I. Qed.
Print Assumptions total_time_in_cswitch_is_bounded_correspondence.
Goal Logic.True. idtac "AUDIT_END total_time_in_cswitch_is_bounded_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN total_time_in_CRPD_is_bounded_correspondence". exact Logic.I. Qed.
Print Assumptions total_time_in_CRPD_is_bounded_correspondence.
Goal Logic.True. idtac "AUDIT_END total_time_in_CRPD_is_bounded_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN no_sched_changes_bounded_overheads_blackout_correspondence". exact Logic.I. Qed.
Print Assumptions no_sched_changes_bounded_overheads_blackout_correspondence.
Goal Logic.True. idtac "AUDIT_END no_sched_changes_bounded_overheads_blackout_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sched_changes_start_busy_pref_bounded_overheads_blackout_correspondence". exact Logic.I. Qed.
Print Assumptions sched_changes_start_busy_pref_bounded_overheads_blackout_correspondence.
Goal Logic.True. idtac "AUDIT_END sched_changes_start_busy_pref_bounded_overheads_blackout_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fin_sched_changes_start_busy_pref_bounded_overheads_blackout_correspondence". exact Logic.I. Qed.
Print Assumptions fin_sched_changes_start_busy_pref_bounded_overheads_blackout_correspondence.
Goal Logic.True. idtac "AUDIT_END fin_sched_changes_start_busy_pref_bounded_overheads_blackout_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN finite_sched_changes_bounded_overheads_blackout_correspondence". exact Logic.I. Qed.
Print Assumptions finite_sched_changes_bounded_overheads_blackout_correspondence.
Goal Logic.True. idtac "AUDIT_END finite_sched_changes_bounded_overheads_blackout_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bob_sc_ar". exact Logic.I. Qed.
Print Assumptions bob_sc_ar.
Goal Logic.True. idtac "AUDIT_END bob_sc_ar". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bob_ovh_svc". exact Logic.I. Qed.
Print Assumptions bob_ovh_svc.
Goal Logic.True. idtac "AUDIT_END bob_ovh_svc". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bob_svc_ar". exact Logic.I. Qed.
Print Assumptions bob_svc_ar.
Goal Logic.True. idtac "AUDIT_END bob_svc_ar". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bob_bool_truth". exact Logic.I. Qed.
Print Assumptions bob_bool_truth.
Goal Logic.True. idtac "AUDIT_END bob_bool_truth". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bob_opt_from_rel". exact Logic.I. Qed.
Print Assumptions bob_opt_from_rel.
Goal Logic.True. idtac "AUDIT_END bob_opt_from_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bob_exists_option". exact Logic.I. Qed.
Print Assumptions bob_exists_option.
Goal Logic.True. idtac "AUDIT_END bob_exists_option". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bob_ovh_sched". exact Logic.I. Qed.
Print Assumptions bob_ovh_sched.
Goal Logic.True. idtac "AUDIT_END bob_ovh_sched". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bob_sc_sched". exact Logic.I. Qed.
Print Assumptions bob_sc_sched.
Goal Logic.True. idtac "AUDIT_END bob_sc_sched". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bob_supply_at_related". exact Logic.I. Qed.
Print Assumptions bob_supply_at_related.
Goal Logic.True. idtac "AUDIT_END bob_supply_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bob_is_blackout_related". exact Logic.I. Qed.
Print Assumptions bob_is_blackout_related.
Goal Logic.True. idtac "AUDIT_END bob_is_blackout_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bob_blackout_related". exact Logic.I. Qed.
Print Assumptions bob_blackout_related.
Goal Logic.True. idtac "AUDIT_END bob_blackout_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bob_total_dispatch_related". exact Logic.I. Qed.
Print Assumptions bob_total_dispatch_related.
Goal Logic.True. idtac "AUDIT_END bob_total_dispatch_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bob_total_context_switch_related". exact Logic.I. Qed.
Print Assumptions bob_total_context_switch_related.
Goal Logic.True. idtac "AUDIT_END bob_total_context_switch_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bob_total_CRPD_related". exact Logic.I. Qed.
Print Assumptions bob_total_CRPD_related.
Goal Logic.True. idtac "AUDIT_END bob_total_CRPD_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bob_nsc_truth". exact Logic.I. Qed.
Print Assumptions bob_nsc_truth.
Goal Logic.True. idtac "AUDIT_END bob_nsc_truth". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bob_sc_truth". exact Logic.I. Qed.
Print Assumptions bob_sc_truth.
Goal Logic.True. idtac "AUDIT_END bob_sc_truth". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bob_count_related". exact Logic.I. Qed.
Print Assumptions bob_count_related.
Goal Logic.True. idtac "AUDIT_END bob_count_related". exact Logic.I. Qed.
