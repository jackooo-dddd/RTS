From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence PreemptionTimeCorrespondence PriorityDrivenCorrespondence PStateCoverHelpers FactsPreemptionHelpers WorkloadCorrespondence PriorityInversionCorrespondence ExistenceCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN job_completes_within_busy_interval_correspondence". exact Logic.I. Qed.
Print Assumptions job_completes_within_busy_interval_correspondence.
Goal Logic.True. idtac "AUDIT_END job_completes_within_busy_interval_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN not_quiet_implies_exists_pending_job_correspondence". exact Logic.I. Qed.
Print Assumptions not_quiet_implies_exists_pending_job_correspondence.
Goal Logic.True. idtac "AUDIT_END not_quiet_implies_exists_pending_job_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN idle_time_implies_quiet_time_at_the_next_time_instant_correspondence". exact Logic.I. Qed.
Print Assumptions idle_time_implies_quiet_time_at_the_next_time_instant_correspondence.
Goal Logic.True. idtac "AUDIT_END idle_time_implies_quiet_time_at_the_next_time_instant_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pending_hp_job_exists_correspondence". exact Logic.I. Qed.
Print Assumptions pending_hp_job_exists_correspondence.
Goal Logic.True. idtac "AUDIT_END pending_hp_job_exists_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN not_quiet_implies_not_idle_correspondence". exact Logic.I. Qed.
Print Assumptions not_quiet_implies_not_idle_correspondence.
Goal Logic.True. idtac "AUDIT_END not_quiet_implies_not_idle_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN hep_jobs_receive_no_service_before_quiet_time_correspondence". exact Logic.I. Qed.
Print Assumptions hep_jobs_receive_no_service_before_quiet_time_correspondence.
Goal Logic.True. idtac "AUDIT_END hep_jobs_receive_no_service_before_quiet_time_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN no_idle_time_within_non_quiet_time_interval_correspondence". exact Logic.I. Qed.
Print Assumptions no_idle_time_within_non_quiet_time_interval_correspondence.
Goal Logic.True. idtac "AUDIT_END no_idle_time_within_non_quiet_time_interval_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN exists_busy_interval_prefix_correspondence". exact Logic.I. Qed.
Print Assumptions exists_busy_interval_prefix_correspondence.
Goal Logic.True. idtac "AUDIT_END exists_busy_interval_prefix_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN busy_interval_has_uninterrupted_service_correspondence". exact Logic.I. Qed.
Print Assumptions busy_interval_has_uninterrupted_service_correspondence.
Goal Logic.True. idtac "AUDIT_END busy_interval_has_uninterrupted_service_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN busy_interval_too_much_workload_correspondence". exact Logic.I. Qed.
Print Assumptions busy_interval_too_much_workload_correspondence.
Goal Logic.True. idtac "AUDIT_END busy_interval_too_much_workload_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN busy_interval_workload_larger_than_interval_correspondence". exact Logic.I. Qed.
Print Assumptions busy_interval_workload_larger_than_interval_correspondence.
Goal Logic.True. idtac "AUDIT_END busy_interval_workload_larger_than_interval_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN busy_interval_is_bounded_correspondence". exact Logic.I. Qed.
Print Assumptions busy_interval_is_bounded_correspondence.
Goal Logic.True. idtac "AUDIT_END busy_interval_is_bounded_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN exists_busy_interval_correspondence". exact Logic.I. Qed.
Print Assumptions exists_busy_interval_correspondence.
Goal Logic.True. idtac "AUDIT_END exists_busy_interval_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN busy_interval_bounds_response_time_correspondence". exact Logic.I. Qed.
Print Assumptions busy_interval_bounds_response_time_correspondence.
Goal Logic.True. idtac "AUDIT_END busy_interval_bounds_response_time_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ex_exists_identity". exact Logic.I. Qed.
Print Assumptions ex_exists_identity.
Goal Logic.True. idtac "AUDIT_END ex_exists_identity". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ex_forall_fun". exact Logic.I. Qed.
Print Assumptions ex_forall_fun.
Goal Logic.True. idtac "AUDIT_END ex_forall_fun". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ex_job_cost_positive_related". exact Logic.I. Qed.
Print Assumptions ex_job_cost_positive_related.
Goal Logic.True. idtac "AUDIT_END ex_job_cost_positive_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ex_unit_service_related". exact Logic.I. Qed.
Print Assumptions ex_unit_service_related.
Goal Logic.True. idtac "AUDIT_END ex_unit_service_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ex_completed_dont_execute_rel". exact Logic.I. Qed.
Print Assumptions ex_completed_dont_execute_rel.
Goal Logic.True. idtac "AUDIT_END ex_completed_dont_execute_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ex_service_of_jobs_related". exact Logic.I. Qed.
Print Assumptions ex_service_of_jobs_related.
Goal Logic.True. idtac "AUDIT_END ex_service_of_jobs_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ex_total_service_related". exact Logic.I. Qed.
Print Assumptions ex_total_service_related.
Goal Logic.True. idtac "AUDIT_END ex_total_service_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ex_quiet_time_related". exact Logic.I. Qed.
Print Assumptions ex_quiet_time_related.
Goal Logic.True. idtac "AUDIT_END ex_quiet_time_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ex_busy_interval_prefix_related". exact Logic.I. Qed.
Print Assumptions ex_busy_interval_prefix_related.
Goal Logic.True. idtac "AUDIT_END ex_busy_interval_prefix_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ex_busy_interval_related". exact Logic.I. Qed.
Print Assumptions ex_busy_interval_related.
Goal Logic.True. idtac "AUDIT_END ex_busy_interval_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ex_priority_inversion_related". exact Logic.I. Qed.
Print Assumptions ex_priority_inversion_related.
Goal Logic.True. idtac "AUDIT_END ex_priority_inversion_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ex_cumulative_priority_inversion_related". exact Logic.I. Qed.
Print Assumptions ex_cumulative_priority_inversion_related.
Goal Logic.True. idtac "AUDIT_END ex_cumulative_priority_inversion_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ex_pi_bounded_related". exact Logic.I. Qed.
Print Assumptions ex_pi_bounded_related.
Goal Logic.True. idtac "AUDIT_END ex_pi_bounded_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ex_service_of_hep_related". exact Logic.I. Qed.
Print Assumptions ex_service_of_hep_related.
Goal Logic.True. idtac "AUDIT_END ex_service_of_hep_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ex_workload_related". exact Logic.I. Qed.
Print Assumptions ex_workload_related.
Goal Logic.True. idtac "AUDIT_END ex_workload_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ex_work_conserving_related". exact Logic.I. Qed.
Print Assumptions ex_work_conserving_related.
Goal Logic.True. idtac "AUDIT_END ex_work_conserving_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ex_work_bearing_related". exact Logic.I. Qed.
Print Assumptions ex_work_bearing_related.
Goal Logic.True. idtac "AUDIT_END ex_work_bearing_related". exact Logic.I. Qed.
