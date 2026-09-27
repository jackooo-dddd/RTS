From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence WorkloadCorrespondence AbstractDefinitionsBaseAdapter ServiceBaseAdapter ServiceNatBoolOperations AbstractDefinitionsArrivalOperations AbstractDefinitionsClasses AbstractDefinitionsNatBoolOperations AbstractDefinitionsIntervalOperations AbstractDefinitionsOperations AbstractDefinitionsSums AbstractDefinitionsLogical ServiceIntervalOperations ServiceScheduleOperations AbstractDefinitionsPendingOperations AbstractDefinitionsTaskOperations AbstractDefinitionsBusyIntervalHelpers AbstractRtaCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN relative_arrival_time_of_job_is_A_correspondence". exact Logic.I. Qed.
Print Assumptions relative_arrival_time_of_job_is_A_correspondence.
Goal Logic.True. idtac "AUDIT_END relative_arrival_time_of_job_is_A_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN relative_time_to_reach_rtct_correspondence". exact Logic.I. Qed.
Print Assumptions relative_time_to_reach_rtct_correspondence.
Goal Logic.True. idtac "AUDIT_END relative_time_to_reach_rtct_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_arrival_eq_t1_plus_A_correspondence". exact Logic.I. Qed.
Print Assumptions job_arrival_eq_t1_plus_A_correspondence.
Goal Logic.True. idtac "AUDIT_END job_arrival_eq_t1_plus_A_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN relative_arrival_is_bounded_correspondence". exact Logic.I. Qed.
Print Assumptions relative_arrival_is_bounded_correspondence.
Goal Logic.True. idtac "AUDIT_END relative_arrival_is_bounded_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN t2_le_arrival_plus_R_1_correspondence". exact Logic.I. Qed.
Print Assumptions t2_le_arrival_plus_R_1_correspondence.
Goal Logic.True. idtac "AUDIT_END t2_le_arrival_plus_R_1_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_completed_by_arrival_plus_R_1_correspondence". exact Logic.I. Qed.
Print Assumptions job_completed_by_arrival_plus_R_1_correspondence.
Goal Logic.True. idtac "AUDIT_END job_completed_by_arrival_plus_R_1_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN t2_le_arrival_plus_R_2_correspondence". exact Logic.I. Qed.
Print Assumptions t2_le_arrival_plus_R_2_correspondence.
Goal Logic.True. idtac "AUDIT_END t2_le_arrival_plus_R_2_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_completed_by_arrival_plus_R_2_correspondence". exact Logic.I. Qed.
Print Assumptions job_completed_by_arrival_plus_R_2_correspondence.
Goal Logic.True. idtac "AUDIT_END job_completed_by_arrival_plus_R_2_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN relative_rtc_time_is_bounded_correspondence". exact Logic.I. Qed.
Print Assumptions relative_rtc_time_is_bounded_correspondence.
Goal Logic.True. idtac "AUDIT_END relative_rtc_time_is_bounded_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_receives_enough_service_1_correspondence". exact Logic.I. Qed.
Print Assumptions job_receives_enough_service_1_correspondence.
Goal Logic.True. idtac "AUDIT_END job_receives_enough_service_1_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_receives_enough_service_2_correspondence". exact Logic.I. Qed.
Print Assumptions job_receives_enough_service_2_correspondence.
Goal Logic.True. idtac "AUDIT_END job_receives_enough_service_2_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_receives_enough_service_3_correspondence". exact Logic.I. Qed.
Print Assumptions job_receives_enough_service_3_correspondence.
Goal Logic.True. idtac "AUDIT_END job_receives_enough_service_3_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_is_completed_by_arrival_plus_R_correspondence". exact Logic.I. Qed.
Print Assumptions job_is_completed_by_arrival_plus_R_correspondence.
Goal Logic.True. idtac "AUDIT_END job_is_completed_by_arrival_plus_R_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN uniprocessor_response_time_bound_correspondence". exact Logic.I. Qed.
Print Assumptions uniprocessor_response_time_bound_correspondence.
Goal Logic.True. idtac "AUDIT_END uniprocessor_response_time_bound_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arta_forall_cover". exact Logic.I. Qed.
Print Assumptions arta_forall_cover.
Goal Logic.True. idtac "AUDIT_END arta_forall_cover". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arta_false_correspondence". exact Logic.I. Qed.
Print Assumptions arta_false_correspondence.
Goal Logic.True. idtac "AUDIT_END arta_false_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arta_or_correspondence". exact Logic.I. Qed.
Print Assumptions arta_or_correspondence.
Goal Logic.True. idtac "AUDIT_END arta_or_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arta_and3_correspondence". exact Logic.I. Qed.
Print Assumptions arta_and3_correspondence.
Goal Logic.True. idtac "AUDIT_END arta_and3_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arta_nat_neq_correspondence". exact Logic.I. Qed.
Print Assumptions arta_nat_neq_correspondence.
Goal Logic.True. idtac "AUDIT_END arta_nat_neq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arta_lean_transport". exact Logic.I. Qed.
Print Assumptions arta_lean_transport.
Goal Logic.True. idtac "AUDIT_END arta_lean_transport". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arta_nat_input". exact Logic.I. Qed.
Print Assumptions arta_nat_input.
Goal Logic.True. idtac "AUDIT_END arta_nat_input". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arta_add_related". exact Logic.I. Qed.
Print Assumptions arta_add_related.
Goal Logic.True. idtac "AUDIT_END arta_add_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arta_sub_related". exact Logic.I. Qed.
Print Assumptions arta_sub_related.
Goal Logic.True. idtac "AUDIT_END arta_sub_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arta_fun_to_target_rel". exact Logic.I. Qed.
Print Assumptions arta_fun_to_target_rel.
Goal Logic.True. idtac "AUDIT_END arta_fun_to_target_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arta_fun_to_source_rel". exact Logic.I. Qed.
Print Assumptions arta_fun_to_source_rel.
Goal Logic.True. idtac "AUDIT_END arta_fun_to_source_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arta_forall_fun". exact Logic.I. Qed.
Print Assumptions arta_forall_fun.
Goal Logic.True. idtac "AUDIT_END arta_forall_fun". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arta_forall_list". exact Logic.I. Qed.
Print Assumptions arta_forall_list.
Goal Logic.True. idtac "AUDIT_END arta_forall_list". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arta_equivalent_rel". exact Logic.I. Qed.
Print Assumptions arta_equivalent_rel.
Goal Logic.True. idtac "AUDIT_END arta_equivalent_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arta_search_space_rel". exact Logic.I. Qed.
Print Assumptions arta_search_space_rel.
Goal Logic.True. idtac "AUDIT_END arta_search_space_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arta_arr_ad". exact Logic.I. Qed.
Print Assumptions arta_arr_ad.
Goal Logic.True. idtac "AUDIT_END arta_arr_ad". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arta_forall_inter". exact Logic.I. Qed.
Print Assumptions arta_forall_inter.
Goal Logic.True. idtac "AUDIT_END arta_forall_inter". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arta_forall_iw". exact Logic.I. Qed.
Print Assumptions arta_forall_iw.
Goal Logic.True. idtac "AUDIT_END arta_forall_iw". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arta_cost_positive_related". exact Logic.I. Qed.
Print Assumptions arta_cost_positive_related.
Goal Logic.True. idtac "AUDIT_END arta_cost_positive_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arta_task_cost_of_job_related". exact Logic.I. Qed.
Print Assumptions arta_task_cost_of_job_related.
Goal Logic.True. idtac "AUDIT_END arta_task_cost_of_job_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arta_valid_job_costs_rel". exact Logic.I. Qed.
Print Assumptions arta_valid_job_costs_rel.
Goal Logic.True. idtac "AUDIT_END arta_valid_job_costs_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arta_response_time_bound_rel". exact Logic.I. Qed.
Print Assumptions arta_response_time_bound_rel.
Goal Logic.True. idtac "AUDIT_END arta_response_time_bound_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arta_bi_rel". exact Logic.I. Qed.
Print Assumptions arta_bi_rel.
Goal Logic.True. idtac "AUDIT_END arta_bi_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arta_wc_rel". exact Logic.I. Qed.
Print Assumptions arta_wc_rel.
Goal Logic.True. idtac "AUDIT_END arta_wc_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arta_bounded_rel". exact Logic.I. Qed.
Print Assumptions arta_bounded_rel.
Goal Logic.True. idtac "AUDIT_END arta_bounded_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arta_job_interference_bounded_rel". exact Logic.I. Qed.
Print Assumptions arta_job_interference_bounded_rel.
Goal Logic.True. idtac "AUDIT_END arta_job_interference_bounded_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arta_ibfp_bounded_rel". exact Logic.I. Qed.
Print Assumptions arta_ibfp_bounded_rel.
Goal Logic.True. idtac "AUDIT_END arta_ibfp_bounded_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arta_ibfnp_bounded_rel". exact Logic.I. Qed.
Print Assumptions arta_ibfnp_bounded_rel.
Goal Logic.True. idtac "AUDIT_END arta_ibfnp_bounded_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arta_ge_param_rel". exact Logic.I. Qed.
Print Assumptions arta_ge_param_rel.
Goal Logic.True. idtac "AUDIT_END arta_ge_param_rel". exact Logic.I. Qed.
