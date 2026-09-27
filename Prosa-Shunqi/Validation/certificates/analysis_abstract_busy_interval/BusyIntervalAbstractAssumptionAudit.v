From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence WorkloadCorrespondence AbstractDefinitionsBaseAdapter ServiceBaseAdapter ServiceNatBoolOperations AbstractDefinitionsArrivalOperations AbstractDefinitionsClasses AbstractDefinitionsNatBoolOperations AbstractDefinitionsIntervalOperations AbstractDefinitionsOperations AbstractDefinitionsSums AbstractDefinitionsLogical ServiceIntervalOperations ServiceScheduleOperations AbstractDefinitionsPendingOperations AbstractDefinitionsTaskOperations AbstractDefinitionsBusyIntervalHelpers BusyIntervalAbstractCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN busy_interval_prefix_case_correspondence". exact Logic.I. Qed.
Print Assumptions busy_interval_prefix_case_correspondence.
Goal Logic.True. idtac "AUDIT_END busy_interval_prefix_case_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN terminating_busy_prefix_is_busy_interval_correspondence". exact Logic.I. Qed.
Print Assumptions terminating_busy_prefix_is_busy_interval_correspondence.
Goal Logic.True. idtac "AUDIT_END terminating_busy_prefix_is_busy_interval_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_completes_within_busy_interval_correspondence". exact Logic.I. Qed.
Print Assumptions job_completes_within_busy_interval_correspondence.
Goal Logic.True. idtac "AUDIT_END job_completes_within_busy_interval_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN no_service_before_busy_interval_correspondence". exact Logic.I. Qed.
Print Assumptions no_service_before_busy_interval_correspondence.
Goal Logic.True. idtac "AUDIT_END no_service_before_busy_interval_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_within_busy_interval_ge_job_cost_correspondence". exact Logic.I. Qed.
Print Assumptions service_within_busy_interval_ge_job_cost_correspondence.
Goal Logic.True. idtac "AUDIT_END service_within_busy_interval_ge_job_cost_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN abstract_busy_interval_arrivals_before_correspondence". exact Logic.I. Qed.
Print Assumptions abstract_busy_interval_arrivals_before_correspondence.
Goal Logic.True. idtac "AUDIT_END abstract_busy_interval_arrivals_before_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN abstract_busy_interval_prefix_job_arrival_correspondence". exact Logic.I. Qed.
Print Assumptions abstract_busy_interval_prefix_job_arrival_correspondence.
Goal Logic.True. idtac "AUDIT_END abstract_busy_interval_prefix_job_arrival_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN abstract_busy_interval_job_arrival_correspondence". exact Logic.I. Qed.
Print Assumptions abstract_busy_interval_job_arrival_correspondence.
Goal Logic.True. idtac "AUDIT_END abstract_busy_interval_job_arrival_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_and_interference_bound_correspondence". exact Logic.I. Qed.
Print Assumptions service_and_interference_bound_correspondence.
Goal Logic.True. idtac "AUDIT_END service_and_interference_bound_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN exists_busy_interval_prefix_correspondence". exact Logic.I. Qed.
Print Assumptions exists_busy_interval_prefix_correspondence.
Goal Logic.True. idtac "AUDIT_END exists_busy_interval_prefix_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN busy_interval_has_uninterrupted_service_correspondence". exact Logic.I. Qed.
Print Assumptions busy_interval_has_uninterrupted_service_correspondence.
Goal Logic.True. idtac "AUDIT_END busy_interval_has_uninterrupted_service_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN busy_interval_too_much_workload_correspondence". exact Logic.I. Qed.
Print Assumptions busy_interval_too_much_workload_correspondence.
Goal Logic.True. idtac "AUDIT_END busy_interval_too_much_workload_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN t1δ_is_quiet_correspondence". exact Logic.I. Qed.
Print Assumptions t1δ_is_quiet_correspondence.
Goal Logic.True. idtac "AUDIT_END t1δ_is_quiet_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN t1δ_is_quiet_contra_correspondence". exact Logic.I. Qed.
Print Assumptions t1δ_is_quiet_contra_correspondence.
Goal Logic.True. idtac "AUDIT_END t1δ_is_quiet_contra_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN busy_interval_is_bounded_correspondence". exact Logic.I. Qed.
Print Assumptions busy_interval_is_bounded_correspondence.
Goal Logic.True. idtac "AUDIT_END busy_interval_is_bounded_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bia_forall_cover". exact Logic.I. Qed.
Print Assumptions bia_forall_cover.
Goal Logic.True. idtac "AUDIT_END bia_forall_cover". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ad_false_correspondence". exact Logic.I. Qed.
Print Assumptions ad_false_correspondence.
Goal Logic.True. idtac "AUDIT_END ad_false_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bia_or_correspondence". exact Logic.I. Qed.
Print Assumptions bia_or_correspondence.
Goal Logic.True. idtac "AUDIT_END bia_or_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bia_lean_transport". exact Logic.I. Qed.
Print Assumptions bia_lean_transport.
Goal Logic.True. idtac "AUDIT_END bia_lean_transport". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bia_nat_input". exact Logic.I. Qed.
Print Assumptions bia_nat_input.
Goal Logic.True. idtac "AUDIT_END bia_nat_input". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bia_succ_related". exact Logic.I. Qed.
Print Assumptions bia_succ_related.
Goal Logic.True. idtac "AUDIT_END bia_succ_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bia_add_related". exact Logic.I. Qed.
Print Assumptions bia_add_related.
Goal Logic.True. idtac "AUDIT_END bia_add_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bia_sched_to_target_rel". exact Logic.I. Qed.
Print Assumptions bia_sched_to_target_rel.
Goal Logic.True. idtac "AUDIT_END bia_sched_to_target_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bia_sched_to_source_rel". exact Logic.I. Qed.
Print Assumptions bia_sched_to_source_rel.
Goal Logic.True. idtac "AUDIT_END bia_sched_to_source_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bia_forall_sched". exact Logic.I. Qed.
Print Assumptions bia_forall_sched.
Goal Logic.True. idtac "AUDIT_END bia_forall_sched". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bia_arr_to_source_rel". exact Logic.I. Qed.
Print Assumptions bia_arr_to_source_rel.
Goal Logic.True. idtac "AUDIT_END bia_arr_to_source_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bia_forall_arr". exact Logic.I. Qed.
Print Assumptions bia_forall_arr.
Goal Logic.True. idtac "AUDIT_END bia_forall_arr". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bia_forall_inter". exact Logic.I. Qed.
Print Assumptions bia_forall_inter.
Goal Logic.True. idtac "AUDIT_END bia_forall_inter". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bia_forall_iw". exact Logic.I. Qed.
Print Assumptions bia_forall_iw.
Goal Logic.True. idtac "AUDIT_END bia_forall_iw". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bia_scheduled_at_related". exact Logic.I. Qed.
Print Assumptions bia_scheduled_at_related.
Goal Logic.True. idtac "AUDIT_END bia_scheduled_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bia_pending_related". exact Logic.I. Qed.
Print Assumptions bia_pending_related.
Goal Logic.True. idtac "AUDIT_END bia_pending_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bia_must_arrive_rel". exact Logic.I. Qed.
Print Assumptions bia_must_arrive_rel.
Goal Logic.True. idtac "AUDIT_END bia_must_arrive_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bia_completed_dont_execute_rel". exact Logic.I. Qed.
Print Assumptions bia_completed_dont_execute_rel.
Goal Logic.True. idtac "AUDIT_END bia_completed_dont_execute_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bia_cost_positive_related". exact Logic.I. Qed.
Print Assumptions bia_cost_positive_related.
Goal Logic.True. idtac "AUDIT_END bia_cost_positive_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bia_unit_service_rel". exact Logic.I. Qed.
Print Assumptions bia_unit_service_rel.
Goal Logic.True. idtac "AUDIT_END bia_unit_service_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bia_bip_rel". exact Logic.I. Qed.
Print Assumptions bia_bip_rel.
Goal Logic.True. idtac "AUDIT_END bia_bip_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bia_bi_rel". exact Logic.I. Qed.
Print Assumptions bia_bi_rel.
Goal Logic.True. idtac "AUDIT_END bia_bi_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bia_not_quiet_rel". exact Logic.I. Qed.
Print Assumptions bia_not_quiet_rel.
Goal Logic.True. idtac "AUDIT_END bia_not_quiet_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bia_open_closed_related". exact Logic.I. Qed.
Print Assumptions bia_open_closed_related.
Goal Logic.True. idtac "AUDIT_END bia_open_closed_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bia_arr_ad". exact Logic.I. Qed.
Print Assumptions bia_arr_ad.
Goal Logic.True. idtac "AUDIT_END bia_arr_ad". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bia_no_quiet_rel". exact Logic.I. Qed.
Print Assumptions bia_no_quiet_rel.
Goal Logic.True. idtac "AUDIT_END bia_no_quiet_rel". exact Logic.I. Qed.
