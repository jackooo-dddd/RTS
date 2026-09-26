From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations IdealServiceOfJobsCorrespondence.

Goal Logic.True. idtac "AUDIT_BEGIN low_service_implies_existence_of_idle_time_rs_correspondence". exact Logic.I. Qed.
Print Assumptions low_service_implies_existence_of_idle_time_rs_correspondence.
Goal Logic.True. idtac "AUDIT_END low_service_implies_existence_of_idle_time_rs_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN low_service_implies_existence_of_idle_time_correspondence". exact Logic.I. Qed.
Print Assumptions low_service_implies_existence_of_idle_time_correspondence.
Goal Logic.True. idtac "AUDIT_END low_service_implies_existence_of_idle_time_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN isj_forall_cover_sprop". exact Logic.I. Qed.
Print Assumptions isj_forall_cover_sprop.
Goal Logic.True. idtac "AUDIT_END isj_forall_cover_sprop". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN isj_lean_transport". exact Logic.I. Qed.
Print Assumptions isj_lean_transport.
Goal Logic.True. idtac "AUDIT_END isj_lean_transport". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN isj_nat_input". exact Logic.I. Qed.
Print Assumptions isj_nat_input.
Goal Logic.True. idtac "AUDIT_END isj_nat_input". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN isj_eq_identity_correspondence". exact Logic.I. Qed.
Print Assumptions isj_eq_identity_correspondence.
Goal Logic.True. idtac "AUDIT_END isj_eq_identity_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN isj_bool_to_nat_related". exact Logic.I. Qed.
Print Assumptions isj_bool_to_nat_related.
Goal Logic.True. idtac "AUDIT_END isj_bool_to_nat_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN isj_sum_filter_related". exact Logic.I. Qed.
Print Assumptions isj_sum_filter_related.
Goal Logic.True. idtac "AUDIT_END isj_sum_filter_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN isj_service_during_related". exact Logic.I. Qed.
Print Assumptions isj_service_during_related.
Goal Logic.True. idtac "AUDIT_END isj_service_during_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN isj_service_of_jobs_predT_related". exact Logic.I. Qed.
Print Assumptions isj_service_of_jobs_predT_related.
Goal Logic.True. idtac "AUDIT_END isj_service_of_jobs_predT_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN isj_scheduled_jobs_at_related". exact Logic.I. Qed.
Print Assumptions isj_scheduled_jobs_at_related.
Goal Logic.True. idtac "AUDIT_END isj_scheduled_jobs_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN isj_is_idle_related". exact Logic.I. Qed.
Print Assumptions isj_is_idle_related.
Goal Logic.True. idtac "AUDIT_END isj_is_idle_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN isj_jobs_come_from_related". exact Logic.I. Qed.
Print Assumptions isj_jobs_come_from_related.
Goal Logic.True. idtac "AUDIT_END isj_jobs_come_from_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN isj_jobs_must_arrive_related". exact Logic.I. Qed.
Print Assumptions isj_jobs_must_arrive_related.
Goal Logic.True. idtac "AUDIT_END isj_jobs_must_arrive_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN isj_idle_exists_related". exact Logic.I. Qed.
Print Assumptions isj_idle_exists_related.
Goal Logic.True. idtac "AUDIT_END isj_idle_exists_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN isj_schedule_fun_to_svc". exact Logic.I. Qed.
Print Assumptions isj_schedule_fun_to_svc.
Goal Logic.True. idtac "AUDIT_END isj_schedule_fun_to_svc". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN isj_schedule_to_target_rel". exact Logic.I. Qed.
Print Assumptions isj_schedule_to_target_rel.
Goal Logic.True. idtac "AUDIT_END isj_schedule_to_target_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN isj_schedule_to_source_rel". exact Logic.I. Qed.
Print Assumptions isj_schedule_to_source_rel.
Goal Logic.True. idtac "AUDIT_END isj_schedule_to_source_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN isj_scheduled_at_related". exact Logic.I. Qed.
Print Assumptions isj_scheduled_at_related.
Goal Logic.True. idtac "AUDIT_END isj_scheduled_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN isj_service_at_related". exact Logic.I. Qed.
Print Assumptions isj_service_at_related.
Goal Logic.True. idtac "AUDIT_END isj_service_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN isj_uniprocessor_related". exact Logic.I. Qed.
Print Assumptions isj_uniprocessor_related.
Goal Logic.True. idtac "AUDIT_END isj_uniprocessor_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN isj_ideal_progress_related". exact Logic.I. Qed.
Print Assumptions isj_ideal_progress_related.
Goal Logic.True. idtac "AUDIT_END isj_ideal_progress_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN isj_supply_in_related". exact Logic.I. Qed.
Print Assumptions isj_supply_in_related.
Goal Logic.True. idtac "AUDIT_END isj_supply_in_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN isj_supply_at_related". exact Logic.I. Qed.
Print Assumptions isj_supply_at_related.
Goal Logic.True. idtac "AUDIT_END isj_supply_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN isj_is_blackout_related". exact Logic.I. Qed.
Print Assumptions isj_is_blackout_related.
Goal Logic.True. idtac "AUDIT_END isj_is_blackout_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN isj_blackout_during_related". exact Logic.I. Qed.
Print Assumptions isj_blackout_during_related.
Goal Logic.True. idtac "AUDIT_END isj_blackout_during_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN isj_fully_consuming_related". exact Logic.I. Qed.
Print Assumptions isj_fully_consuming_related.
Goal Logic.True. idtac "AUDIT_END isj_fully_consuming_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN isj_forall_cover_type". exact Logic.I. Qed.
Print Assumptions isj_forall_cover_type.
Goal Logic.True. idtac "AUDIT_END isj_forall_cover_type". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN isj_bool_rel_true". exact Logic.I. Qed.
Print Assumptions isj_bool_rel_true.
Goal Logic.True. idtac "AUDIT_END isj_bool_rel_true". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN isj_bool_false_of_rocq". exact Logic.I. Qed.
Print Assumptions isj_bool_false_of_rocq.
Goal Logic.True. idtac "AUDIT_END isj_bool_false_of_rocq". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN isj_map_values_canonical". exact Logic.I. Qed.
Print Assumptions isj_map_values_canonical.
Goal Logic.True. idtac "AUDIT_END isj_map_values_canonical". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN isj_ar_svc_list_eq". exact Logic.I. Qed.
Print Assumptions isj_ar_svc_list_eq.
Goal Logic.True. idtac "AUDIT_END isj_ar_svc_list_eq". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN isj_psr_scheduled_in_related". exact Logic.I. Qed.
Print Assumptions isj_psr_scheduled_in_related.
Goal Logic.True. idtac "AUDIT_END isj_psr_scheduled_in_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN isj_psr_sched_to_target_rel". exact Logic.I. Qed.
Print Assumptions isj_psr_sched_to_target_rel.
Goal Logic.True. idtac "AUDIT_END isj_psr_sched_to_target_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN isj_psr_sched_to_source_rel". exact Logic.I. Qed.
Print Assumptions isj_psr_sched_to_source_rel.
Goal Logic.True. idtac "AUDIT_END isj_psr_sched_to_source_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN isj_psr_scheduled_at_related". exact Logic.I. Qed.
Print Assumptions isj_psr_scheduled_at_related.
Goal Logic.True. idtac "AUDIT_END isj_psr_scheduled_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN isj_psr_service_at_related". exact Logic.I. Qed.
Print Assumptions isj_psr_service_at_related.
Goal Logic.True. idtac "AUDIT_END isj_psr_service_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN isj_psr_uniprocessor_related". exact Logic.I. Qed.
Print Assumptions isj_psr_uniprocessor_related.
Goal Logic.True. idtac "AUDIT_END isj_psr_uniprocessor_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN isj_psr_ideal_progress_related". exact Logic.I. Qed.
Print Assumptions isj_psr_ideal_progress_related.
Goal Logic.True. idtac "AUDIT_END isj_psr_ideal_progress_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN isj_enum_nodup". exact Logic.I. Qed.
Print Assumptions isj_enum_nodup.
Goal Logic.True. idtac "AUDIT_END isj_enum_nodup". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN isj_enum_complete". exact Logic.I. Qed.
Print Assumptions isj_enum_complete.
Goal Logic.True. idtac "AUDIT_END isj_enum_complete". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN isj_law_le". exact Logic.I. Qed.
Print Assumptions isj_law_le.
Goal Logic.True. idtac "AUDIT_END isj_law_le". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN isj_law_zero". exact Logic.I. Qed.
Print Assumptions isj_law_zero.
Goal Logic.True. idtac "AUDIT_END isj_law_zero". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN isj_to_target_service_in". exact Logic.I. Qed.
Print Assumptions isj_to_target_service_in.
Goal Logic.True. idtac "AUDIT_END isj_to_target_service_in". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN isj_to_target_supply_in". exact Logic.I. Qed.
Print Assumptions isj_to_target_supply_in.
Goal Logic.True. idtac "AUDIT_END isj_to_target_supply_in". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN isj_core_eqP". exact Logic.I. Qed.
Print Assumptions isj_core_eqP.
Goal Logic.True. idtac "AUDIT_END isj_core_eqP". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN isj_core_list_rel". exact Logic.I. Qed.
Print Assumptions isj_core_list_rel.
Goal Logic.True. idtac "AUDIT_END isj_core_list_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN isj_core_list_uniq". exact Logic.I. Qed.
Print Assumptions isj_core_list_uniq.
Goal Logic.True. idtac "AUDIT_END isj_core_list_uniq". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN isj_core_list_complete". exact Logic.I. Qed.
Print Assumptions isj_core_list_complete.
Goal Logic.True. idtac "AUDIT_END isj_core_list_complete". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN isj_core_enum_map". exact Logic.I. Qed.
Print Assumptions isj_core_enum_map.
Goal Logic.True. idtac "AUDIT_END isj_core_enum_map". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN isj_src_law_le". exact Logic.I. Qed.
Print Assumptions isj_src_law_le.
Goal Logic.True. idtac "AUDIT_END isj_src_law_le". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN isj_src_law_zero". exact Logic.I. Qed.
Print Assumptions isj_src_law_zero.
Goal Logic.True. idtac "AUDIT_END isj_src_law_zero". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN isj_core_enumeration_rel". exact Logic.I. Qed.
Print Assumptions isj_core_enumeration_rel.
Goal Logic.True. idtac "AUDIT_END isj_core_enumeration_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN isj_to_source_service_in". exact Logic.I. Qed.
Print Assumptions isj_to_source_service_in.
Goal Logic.True. idtac "AUDIT_END isj_to_source_service_in". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN isj_to_source_supply_in". exact Logic.I. Qed.
Print Assumptions isj_to_source_supply_in.
Goal Logic.True. idtac "AUDIT_END isj_to_source_supply_in". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN isj_arrival_sequence_to_source_rel". exact Logic.I. Qed.
Print Assumptions isj_arrival_sequence_to_source_rel.
Goal Logic.True. idtac "AUDIT_END isj_arrival_sequence_to_source_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN isj_exists_elim_sprop". exact Logic.I. Qed.
Print Assumptions isj_exists_elim_sprop.
Goal Logic.True. idtac "AUDIT_END isj_exists_elim_sprop". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN isj_rel_to_target". exact Logic.I. Qed.
Print Assumptions isj_rel_to_target.
Goal Logic.True. idtac "AUDIT_END isj_rel_to_target". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN isj_rel_to_source". exact Logic.I. Qed.
Print Assumptions isj_rel_to_source.
Goal Logic.True. idtac "AUDIT_END isj_rel_to_source". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN isj_cover_pstate". exact Logic.I. Qed.
Print Assumptions isj_cover_pstate.
Goal Logic.True. idtac "AUDIT_END isj_cover_pstate". exact Logic.I. Qed.
