From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence IdealUniSchedulerCorrespondence EdfDefinitionsHelpers EdfTransCorrespondence FactsEdfOptCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN t1_relevant_correspondence". exact Logic.I. Qed.
Print Assumptions t1_relevant_correspondence.
Goal Logic.True. idtac "AUDIT_END t1_relevant_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsc_search_successful_correspondence". exact Logic.I. Qed.
Print Assumptions fsc_search_successful_correspondence.
Goal Logic.True. idtac "AUDIT_END fsc_search_successful_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsc_search_result_correspondence". exact Logic.I. Qed.
Print Assumptions fsc_search_result_correspondence.
Goal Logic.True. idtac "AUDIT_END fsc_search_result_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsc_not_idle_correspondence". exact Logic.I. Qed.
Print Assumptions fsc_not_idle_correspondence.
Goal Logic.True. idtac "AUDIT_END fsc_not_idle_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsc_found_job_arrival_correspondence". exact Logic.I. Qed.
Print Assumptions fsc_found_job_arrival_correspondence.
Goal Logic.True. idtac "AUDIT_END fsc_found_job_arrival_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsc_range_correspondence". exact Logic.I. Qed.
Print Assumptions fsc_range_correspondence.
Goal Logic.True. idtac "AUDIT_END fsc_range_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsc_range1_correspondence". exact Logic.I. Qed.
Print Assumptions fsc_range1_correspondence.
Goal Logic.True. idtac "AUDIT_END fsc_range1_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsc_found_job_deadline_correspondence". exact Logic.I. Qed.
Print Assumptions fsc_found_job_deadline_correspondence.
Goal Logic.True. idtac "AUDIT_END fsc_found_job_deadline_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsc_no_later_deadline_correspondence". exact Logic.I. Qed.
Print Assumptions fsc_no_later_deadline_correspondence.
Goal Logic.True. idtac "AUDIT_END fsc_no_later_deadline_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN scheduled_job_in_sched_has_later_deadline_correspondence". exact Logic.I. Qed.
Print Assumptions scheduled_job_in_sched_has_later_deadline_correspondence.
Goal Logic.True. idtac "AUDIT_END scheduled_job_in_sched_has_later_deadline_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN mea_completed_jobs_correspondence". exact Logic.I. Qed.
Print Assumptions mea_completed_jobs_correspondence.
Goal Logic.True. idtac "AUDIT_END mea_completed_jobs_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN mea_no_deadline_misses_correspondence". exact Logic.I. Qed.
Print Assumptions mea_no_deadline_misses_correspondence.
Goal Logic.True. idtac "AUDIT_END mea_no_deadline_misses_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN mea_scheduled_job_has_later_deadline_correspondence". exact Logic.I. Qed.
Print Assumptions mea_scheduled_job_has_later_deadline_correspondence.
Goal Logic.True. idtac "AUDIT_END mea_scheduled_job_has_later_deadline_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN mea_guarantee_dl_orig_correspondence". exact Logic.I. Qed.
Print Assumptions mea_guarantee_dl_orig_correspondence.
Goal Logic.True. idtac "AUDIT_END mea_guarantee_dl_orig_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN mea_guarantee_fsc_is_j_edf_correspondence". exact Logic.I. Qed.
Print Assumptions mea_guarantee_fsc_is_j_edf_correspondence.
Goal Logic.True. idtac "AUDIT_END mea_guarantee_fsc_is_j_edf_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN mea_guarantee_deadlines_correspondence". exact Logic.I. Qed.
Print Assumptions mea_guarantee_deadlines_correspondence.
Goal Logic.True. idtac "AUDIT_END mea_guarantee_deadlines_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN mea_guarantee_case_t'_past_deadline_correspondence". exact Logic.I. Qed.
Print Assumptions mea_guarantee_case_t'_past_deadline_correspondence.
Goal Logic.True. idtac "AUDIT_END mea_guarantee_case_t'_past_deadline_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN mea_guarantee_case_t'_before_deadline_correspondence". exact Logic.I. Qed.
Print Assumptions mea_guarantee_case_t'_before_deadline_correspondence.
Goal Logic.True. idtac "AUDIT_END mea_guarantee_case_t'_before_deadline_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN make_edf_at_guarantee_correspondence". exact Logic.I. Qed.
Print Assumptions make_edf_at_guarantee_correspondence.
Goal Logic.True. idtac "AUDIT_END make_edf_at_guarantee_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN mea_jobs_must_arrive_correspondence". exact Logic.I. Qed.
Print Assumptions mea_jobs_must_arrive_correspondence.
Goal Logic.True. idtac "AUDIT_END mea_jobs_must_arrive_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN mea_job_scheduled_correspondence". exact Logic.I. Qed.
Print Assumptions mea_job_scheduled_correspondence.
Goal Logic.True. idtac "AUDIT_END mea_job_scheduled_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN mea_job_scheduled'_correspondence". exact Logic.I. Qed.
Print Assumptions mea_job_scheduled'_correspondence.
Goal Logic.True. idtac "AUDIT_END mea_job_scheduled'_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN mea_jobs_come_from_arrival_sequence_correspondence". exact Logic.I. Qed.
Print Assumptions mea_jobs_come_from_arrival_sequence_correspondence.
Goal Logic.True. idtac "AUDIT_END mea_jobs_come_from_arrival_sequence_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN mea_EDF_widen_correspondence". exact Logic.I. Qed.
Print Assumptions mea_EDF_widen_correspondence.
Goal Logic.True. idtac "AUDIT_END mea_EDF_widen_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN edf_prefix_well_formedness_correspondence". exact Logic.I. Qed.
Print Assumptions edf_prefix_well_formedness_correspondence.
Goal Logic.True. idtac "AUDIT_END edf_prefix_well_formedness_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN edf_prefix_jobs_must_arrive_correspondence". exact Logic.I. Qed.
Print Assumptions edf_prefix_jobs_must_arrive_correspondence.
Goal Logic.True. idtac "AUDIT_END edf_prefix_jobs_must_arrive_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN edf_prefix_scheduled_job_has_later_deadline_correspondence". exact Logic.I. Qed.
Print Assumptions edf_prefix_scheduled_job_has_later_deadline_correspondence.
Goal Logic.True. idtac "AUDIT_END edf_prefix_scheduled_job_has_later_deadline_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN edf_prefix_job_scheduled_correspondence". exact Logic.I. Qed.
Print Assumptions edf_prefix_job_scheduled_correspondence.
Goal Logic.True. idtac "AUDIT_END edf_prefix_job_scheduled_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN edf_prefix_job_scheduled'_correspondence". exact Logic.I. Qed.
Print Assumptions edf_prefix_job_scheduled'_correspondence.
Goal Logic.True. idtac "AUDIT_END edf_prefix_job_scheduled'_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN edf_prefix_jobs_come_from_arrival_sequence_correspondence". exact Logic.I. Qed.
Print Assumptions edf_prefix_jobs_come_from_arrival_sequence_correspondence.
Goal Logic.True. idtac "AUDIT_END edf_prefix_jobs_come_from_arrival_sequence_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN edf_prefix_guarantee_correspondence". exact Logic.I. Qed.
Print Assumptions edf_prefix_guarantee_correspondence.
Goal Logic.True. idtac "AUDIT_END edf_prefix_guarantee_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN edf_prefix_inclusion_correspondence". exact Logic.I. Qed.
Print Assumptions edf_prefix_inclusion_correspondence.
Goal Logic.True. idtac "AUDIT_END edf_prefix_inclusion_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN edf_finite_prefix_correspondence". exact Logic.I. Qed.
Print Assumptions edf_finite_prefix_correspondence.
Goal Logic.True. idtac "AUDIT_END edf_finite_prefix_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN edf_transform_ensures_edf_correspondence". exact Logic.I. Qed.
Print Assumptions edf_transform_ensures_edf_correspondence.
Goal Logic.True. idtac "AUDIT_END edf_transform_ensures_edf_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN edf_transform_completed_jobs_dont_execute_correspondence". exact Logic.I. Qed.
Print Assumptions edf_transform_completed_jobs_dont_execute_correspondence.
Goal Logic.True. idtac "AUDIT_END edf_transform_completed_jobs_dont_execute_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN edf_transform_jobs_must_arrive_correspondence". exact Logic.I. Qed.
Print Assumptions edf_transform_jobs_must_arrive_correspondence.
Goal Logic.True. idtac "AUDIT_END edf_transform_jobs_must_arrive_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN edf_transform_deadlines_met_correspondence". exact Logic.I. Qed.
Print Assumptions edf_transform_deadlines_met_correspondence.
Goal Logic.True. idtac "AUDIT_END edf_transform_deadlines_met_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN edf_transform_job_scheduled_correspondence". exact Logic.I. Qed.
Print Assumptions edf_transform_job_scheduled_correspondence.
Goal Logic.True. idtac "AUDIT_END edf_transform_job_scheduled_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN edf_transform_job_scheduled'_correspondence". exact Logic.I. Qed.
Print Assumptions edf_transform_job_scheduled'_correspondence.
Goal Logic.True. idtac "AUDIT_END edf_transform_job_scheduled'_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN edf_transform_jobs_come_from_arrival_sequence_correspondence". exact Logic.I. Qed.
Print Assumptions edf_transform_jobs_come_from_arrival_sequence_correspondence.
Goal Logic.True. idtac "AUDIT_END edf_transform_jobs_come_from_arrival_sequence_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN edf_schedule_is_valid_correspondence". exact Logic.I. Qed.
Print Assumptions edf_schedule_is_valid_correspondence.
Goal Logic.True. idtac "AUDIT_END edf_schedule_is_valid_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN edf_schedule_meets_all_deadlines_correspondence". exact Logic.I. Qed.
Print Assumptions edf_schedule_meets_all_deadlines_correspondence.
Goal Logic.True. idtac "AUDIT_END edf_schedule_meets_all_deadlines_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN edf_schedule_meets_all_deadlines_wrt_arrivals_correspondence". exact Logic.I. Qed.
Print Assumptions edf_schedule_meets_all_deadlines_wrt_arrivals_correspondence.
Goal Logic.True. idtac "AUDIT_END edf_schedule_meets_all_deadlines_wrt_arrivals_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN feo_optnat_roundtrip". exact Logic.I. Qed.
Print Assumptions feo_optnat_roundtrip.
Goal Logic.True. idtac "AUDIT_END feo_optnat_roundtrip". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN feo_optnat_some_eq". exact Logic.I. Qed.
Print Assumptions feo_optnat_some_eq.
Goal Logic.True. idtac "AUDIT_END feo_optnat_some_eq". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN feo_arr_to_source_rel". exact Logic.I. Qed.
Print Assumptions feo_arr_to_source_rel.
Goal Logic.True. idtac "AUDIT_END feo_arr_to_source_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN feo_forall_arr". exact Logic.I. Qed.
Print Assumptions feo_forall_arr.
Goal Logic.True. idtac "AUDIT_END feo_forall_arr". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN feo_fsc". exact Logic.I. Qed.
Print Assumptions feo_fsc.
Goal Logic.True. idtac "AUDIT_END feo_fsc". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN feo_mea". exact Logic.I. Qed.
Print Assumptions feo_mea.
Goal Logic.True. idtac "AUDIT_END feo_mea". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN feo_prefix". exact Logic.I. Qed.
Print Assumptions feo_prefix.
Goal Logic.True. idtac "AUDIT_END feo_prefix". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN feo_transform". exact Logic.I. Qed.
Print Assumptions feo_transform.
Goal Logic.True. idtac "AUDIT_END feo_transform". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN feo_search_arg". exact Logic.I. Qed.
Print Assumptions feo_search_arg.
Goal Logic.True. idtac "AUDIT_END feo_search_arg". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN feo_sched_at". exact Logic.I. Qed.
Print Assumptions feo_sched_at.
Goal Logic.True. idtac "AUDIT_END feo_sched_at". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN feo_must_rel". exact Logic.I. Qed.
Print Assumptions feo_must_rel.
Goal Logic.True. idtac "AUDIT_END feo_must_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN feo_cde_rel". exact Logic.I. Qed.
Print Assumptions feo_cde_rel.
Goal Logic.True. idtac "AUDIT_END feo_cde_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN feo_meets_rel". exact Logic.I. Qed.
Print Assumptions feo_meets_rel.
Goal Logic.True. idtac "AUDIT_END feo_meets_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN feo_dm_rel". exact Logic.I. Qed.
Print Assumptions feo_dm_rel.
Goal Logic.True. idtac "AUDIT_END feo_dm_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN feo_EDF_at_rel". exact Logic.I. Qed.
Print Assumptions feo_EDF_at_rel.
Goal Logic.True. idtac "AUDIT_END feo_EDF_at_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN feo_EDF_schedule_rel". exact Logic.I. Qed.
Print Assumptions feo_EDF_schedule_rel.
Goal Logic.True. idtac "AUDIT_END feo_EDF_schedule_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN feo_ready_rel". exact Logic.I. Qed.
Print Assumptions feo_ready_rel.
Goal Logic.True. idtac "AUDIT_END feo_ready_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN feo_jcf_rel". exact Logic.I. Qed.
Print Assumptions feo_jcf_rel.
Goal Logic.True. idtac "AUDIT_END feo_jcf_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN feo_valid_rel". exact Logic.I. Qed.
Print Assumptions feo_valid_rel.
Goal Logic.True. idtac "AUDIT_END feo_valid_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN feo_doa_rel". exact Logic.I. Qed.
Print Assumptions feo_doa_rel.
Goal Logic.True. idtac "AUDIT_END feo_doa_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN feo_idp_rel". exact Logic.I. Qed.
Print Assumptions feo_idp_rel.
Goal Logic.True. idtac "AUDIT_END feo_idp_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN feo_wf". exact Logic.I. Qed.
Print Assumptions feo_wf.
Goal Logic.True. idtac "AUDIT_END feo_wf". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN feo_fsc_prefix". exact Logic.I. Qed.
Print Assumptions feo_fsc_prefix.
Goal Logic.True. idtac "AUDIT_END feo_fsc_prefix". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN feo_guarantee_prefix". exact Logic.I. Qed.
Print Assumptions feo_guarantee_prefix.
Goal Logic.True. idtac "AUDIT_END feo_guarantee_prefix". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN feo_sched_exists". exact Logic.I. Qed.
Print Assumptions feo_sched_exists.
Goal Logic.True. idtac "AUDIT_END feo_sched_exists". exact Logic.I. Qed.
