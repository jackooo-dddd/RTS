From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence WorkloadCorrespondence ServiceOfJobsCorrespondence FactsServiceOfJobsCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN service_of_jobs_cat_scheduling_interval_correspondence". exact Logic.I. Qed.
Print Assumptions service_of_jobs_cat_scheduling_interval_correspondence.
Goal Logic.True. idtac "AUDIT_END service_of_jobs_cat_scheduling_interval_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_of_jobs_cat_arrival_interval_correspondence". exact Logic.I. Qed.
Print Assumptions service_of_jobs_cat_arrival_interval_correspondence.
Goal Logic.True. idtac "AUDIT_END service_of_jobs_cat_arrival_interval_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_of_jobs_case_on_pred_correspondence". exact Logic.I. Qed.
Print Assumptions service_of_jobs_case_on_pred_correspondence.
Goal Logic.True. idtac "AUDIT_END service_of_jobs_case_on_pred_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_of_jobs_negate_pred_correspondence". exact Logic.I. Qed.
Print Assumptions service_of_jobs_negate_pred_correspondence.
Goal Logic.True. idtac "AUDIT_END service_of_jobs_negate_pred_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_of_jobs_pred_impl_correspondence". exact Logic.I. Qed.
Print Assumptions service_of_jobs_pred_impl_correspondence.
Goal Logic.True. idtac "AUDIT_END service_of_jobs_pred_impl_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_of_jobs_equiv_pred_correspondence". exact Logic.I. Qed.
Print Assumptions service_of_jobs_equiv_pred_correspondence.
Goal Logic.True. idtac "AUDIT_END service_of_jobs_equiv_pred_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_of_jobs_sum_over_time_interval_correspondence". exact Logic.I. Qed.
Print Assumptions service_of_jobs_sum_over_time_interval_correspondence.
Goal Logic.True. idtac "AUDIT_END service_of_jobs_sum_over_time_interval_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_of_jobs_pred0_correspondence". exact Logic.I. Qed.
Print Assumptions service_of_jobs_pred0_correspondence.
Goal Logic.True. idtac "AUDIT_END service_of_jobs_pred0_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_of_jobs_nsched_or_unsat_correspondence". exact Logic.I. Qed.
Print Assumptions service_of_jobs_nsched_or_unsat_correspondence.
Goal Logic.True. idtac "AUDIT_END service_of_jobs_nsched_or_unsat_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_of_jobs_geq_correspondence". exact Logic.I. Qed.
Print Assumptions service_of_jobs_geq_correspondence.
Goal Logic.True. idtac "AUDIT_END service_of_jobs_geq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_of_jobs_cat_last_correspondence". exact Logic.I. Qed.
Print Assumptions service_of_jobs_cat_last_correspondence.
Goal Logic.True. idtac "AUDIT_END service_of_jobs_cat_last_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_plus_ahep_eq_service_hep_correspondence". exact Logic.I. Qed.
Print Assumptions service_plus_ahep_eq_service_hep_correspondence.
Goal Logic.True. idtac "AUDIT_END service_plus_ahep_eq_service_hep_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_of_jobs_le_workload_correspondence". exact Logic.I. Qed.
Print Assumptions service_of_jobs_le_workload_correspondence.
Goal Logic.True. idtac "AUDIT_END service_of_jobs_le_workload_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN workload_eq_service_impl_all_jobs_have_completed_correspondence". exact Logic.I. Qed.
Print Assumptions workload_eq_service_impl_all_jobs_have_completed_correspondence.
Goal Logic.True. idtac "AUDIT_END workload_eq_service_impl_all_jobs_have_completed_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN all_jobs_have_completed_impl_workload_eq_service_correspondence". exact Logic.I. Qed.
Print Assumptions all_jobs_have_completed_impl_workload_eq_service_correspondence.
Goal Logic.True. idtac "AUDIT_END all_jobs_have_completed_impl_workload_eq_service_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN all_jobs_have_completed_equiv_workload_eq_service_correspondence". exact Logic.I. Qed.
Print Assumptions all_jobs_have_completed_equiv_workload_eq_service_correspondence.
Goal Logic.True. idtac "AUDIT_END all_jobs_have_completed_equiv_workload_eq_service_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_of_jobs_le_1_correspondence". exact Logic.I. Qed.
Print Assumptions service_of_jobs_le_1_correspondence.
Goal Logic.True. idtac "AUDIT_END service_of_jobs_le_1_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_of_jobs_le_length_of_interval_correspondence". exact Logic.I. Qed.
Print Assumptions service_of_jobs_le_length_of_interval_correspondence.
Goal Logic.True. idtac "AUDIT_END service_of_jobs_le_length_of_interval_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_of_jobs_le_length_of_interval'_correspondence". exact Logic.I. Qed.
Print Assumptions service_of_jobs_le_length_of_interval'_correspondence.
Goal Logic.True. idtac "AUDIT_END service_of_jobs_le_length_of_interval'_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_of_jobs_at_scheduled1_correspondence". exact Logic.I. Qed.
Print Assumptions service_of_jobs_at_scheduled1_correspondence.
Goal Logic.True. idtac "AUDIT_END service_of_jobs_at_scheduled1_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_of_jobs_always_scheduled_correspondence". exact Logic.I. Qed.
Print Assumptions service_of_jobs_always_scheduled_correspondence.
Goal Logic.True. idtac "AUDIT_END service_of_jobs_always_scheduled_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cumulative_pred_served_eq_service_correspondence". exact Logic.I. Qed.
Print Assumptions cumulative_pred_served_eq_service_correspondence.
Goal Logic.True. idtac "AUDIT_END cumulative_pred_served_eq_service_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsoj_forall_cover_sprop". exact Logic.I. Qed.
Print Assumptions fsoj_forall_cover_sprop.
Goal Logic.True. idtac "AUDIT_END fsoj_forall_cover_sprop". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsoj_lean_transport". exact Logic.I. Qed.
Print Assumptions fsoj_lean_transport.
Goal Logic.True. idtac "AUDIT_END fsoj_lean_transport". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsoj_nat_input". exact Logic.I. Qed.
Print Assumptions fsoj_nat_input.
Goal Logic.True. idtac "AUDIT_END fsoj_nat_input". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsoj_eq_correspondence". exact Logic.I. Qed.
Print Assumptions fsoj_eq_correspondence.
Goal Logic.True. idtac "AUDIT_END fsoj_eq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsoj_bool_eq_correspondence". exact Logic.I. Qed.
Print Assumptions fsoj_bool_eq_correspondence.
Goal Logic.True. idtac "AUDIT_END fsoj_bool_eq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsoj_exists_identity". exact Logic.I. Qed.
Print Assumptions fsoj_exists_identity.
Goal Logic.True. idtac "AUDIT_END fsoj_exists_identity". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsoj_bool_to_nat_related". exact Logic.I. Qed.
Print Assumptions fsoj_bool_to_nat_related.
Goal Logic.True. idtac "AUDIT_END fsoj_bool_to_nat_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsoj_window_le_le". exact Logic.I. Qed.
Print Assumptions fsoj_window_le_le.
Goal Logic.True. idtac "AUDIT_END fsoj_window_le_le". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsoj_window_le_lt". exact Logic.I. Qed.
Print Assumptions fsoj_window_le_lt.
Goal Logic.True. idtac "AUDIT_END fsoj_window_le_lt". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsoj_has_canonical". exact Logic.I. Qed.
Print Assumptions fsoj_has_canonical.
Goal Logic.True. idtac "AUDIT_END fsoj_has_canonical". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsoj_has_related". exact Logic.I. Qed.
Print Assumptions fsoj_has_related.
Goal Logic.True. idtac "AUDIT_END fsoj_has_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsoj_schedule_to_target_rel". exact Logic.I. Qed.
Print Assumptions fsoj_schedule_to_target_rel.
Goal Logic.True. idtac "AUDIT_END fsoj_schedule_to_target_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsoj_schedule_to_source_rel". exact Logic.I. Qed.
Print Assumptions fsoj_schedule_to_source_rel.
Goal Logic.True. idtac "AUDIT_END fsoj_schedule_to_source_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsoj_arrival_sequence_to_source_rel". exact Logic.I. Qed.
Print Assumptions fsoj_arrival_sequence_to_source_rel.
Goal Logic.True. idtac "AUDIT_END fsoj_arrival_sequence_to_source_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsoj_pred_to_source_rel". exact Logic.I. Qed.
Print Assumptions fsoj_pred_to_source_rel.
Goal Logic.True. idtac "AUDIT_END fsoj_pred_to_source_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsoj_list_to_target_rel". exact Logic.I. Qed.
Print Assumptions fsoj_list_to_target_rel.
Goal Logic.True. idtac "AUDIT_END fsoj_list_to_target_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsoj_list_to_source_rel". exact Logic.I. Qed.
Print Assumptions fsoj_list_to_source_rel.
Goal Logic.True. idtac "AUDIT_END fsoj_list_to_source_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsoj_jlfp_to_target_rel". exact Logic.I. Qed.
Print Assumptions fsoj_jlfp_to_target_rel.
Goal Logic.True. idtac "AUDIT_END fsoj_jlfp_to_target_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsoj_jlfp_to_source_rel". exact Logic.I. Qed.
Print Assumptions fsoj_jlfp_to_source_rel.
Goal Logic.True. idtac "AUDIT_END fsoj_jlfp_to_source_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsoj_unit_service_related". exact Logic.I. Qed.
Print Assumptions fsoj_unit_service_related.
Goal Logic.True. idtac "AUDIT_END fsoj_unit_service_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsoj_ideal_progress_related". exact Logic.I. Qed.
Print Assumptions fsoj_ideal_progress_related.
Goal Logic.True. idtac "AUDIT_END fsoj_ideal_progress_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsoj_uniprocessor_related". exact Logic.I. Qed.
Print Assumptions fsoj_uniprocessor_related.
Goal Logic.True. idtac "AUDIT_END fsoj_uniprocessor_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsoj_jobs_must_arrive_related". exact Logic.I. Qed.
Print Assumptions fsoj_jobs_must_arrive_related.
Goal Logic.True. idtac "AUDIT_END fsoj_jobs_must_arrive_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsoj_completed_jobs_dont_execute_related". exact Logic.I. Qed.
Print Assumptions fsoj_completed_jobs_dont_execute_related.
Goal Logic.True. idtac "AUDIT_END fsoj_completed_jobs_dont_execute_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsoj_soj_related". exact Logic.I. Qed.
Print Assumptions fsoj_soj_related.
Goal Logic.True. idtac "AUDIT_END fsoj_soj_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsoj_soj_at_related". exact Logic.I. Qed.
Print Assumptions fsoj_soj_at_related.
Goal Logic.True. idtac "AUDIT_END fsoj_soj_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsoj_receives_service_at_related". exact Logic.I. Qed.
Print Assumptions fsoj_receives_service_at_related.
Goal Logic.True. idtac "AUDIT_END fsoj_receives_service_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsoj_served_jobs_at_related". exact Logic.I. Qed.
Print Assumptions fsoj_served_jobs_at_related.
Goal Logic.True. idtac "AUDIT_END fsoj_served_jobs_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsoj_quiet_time_related". exact Logic.I. Qed.
Print Assumptions fsoj_quiet_time_related.
Goal Logic.True. idtac "AUDIT_END fsoj_quiet_time_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsoj_reflexive_related". exact Logic.I. Qed.
Print Assumptions fsoj_reflexive_related.
Goal Logic.True. idtac "AUDIT_END fsoj_reflexive_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsoj_all_completed_related". exact Logic.I. Qed.
Print Assumptions fsoj_all_completed_related.
Goal Logic.True. idtac "AUDIT_END fsoj_all_completed_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsoj_workload_eq_service_related". exact Logic.I. Qed.
Print Assumptions fsoj_workload_eq_service_related.
Goal Logic.True. idtac "AUDIT_END fsoj_workload_eq_service_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsoj_some_scheduled_related". exact Logic.I. Qed.
Print Assumptions fsoj_some_scheduled_related.
Goal Logic.True. idtac "AUDIT_END fsoj_some_scheduled_related". exact Logic.I. Qed.
