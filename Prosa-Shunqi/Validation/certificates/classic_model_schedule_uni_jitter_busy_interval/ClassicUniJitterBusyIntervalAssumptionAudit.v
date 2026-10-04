From FoundationCertificates Require Import ClassicUniJitterBusyIntervalCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN BusyInterval_quiet_time_correspondence". exact Logic.I. Qed.
Print Assumptions BusyInterval_quiet_time_correspondence.
Goal Logic.True. idtac "AUDIT_END BusyInterval_quiet_time_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN BusyInterval_busy_interval_prefix_correspondence". exact Logic.I. Qed.
Print Assumptions BusyInterval_busy_interval_prefix_correspondence.
Goal Logic.True. idtac "AUDIT_END BusyInterval_busy_interval_prefix_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN BusyInterval_busy_interval_correspondence". exact Logic.I. Qed.
Print Assumptions BusyInterval_busy_interval_correspondence.
Goal Logic.True. idtac "AUDIT_END BusyInterval_busy_interval_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN BusyInterval_job_completes_within_busy_interval_correspondence". exact Logic.I. Qed.
Print Assumptions BusyInterval_job_completes_within_busy_interval_correspondence.
Goal Logic.True. idtac "AUDIT_END BusyInterval_job_completes_within_busy_interval_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN BusyInterval_job_arrives_within_busy_interval_correspondence". exact Logic.I. Qed.
Print Assumptions BusyInterval_job_arrives_within_busy_interval_correspondence.
Goal Logic.True. idtac "AUDIT_END BusyInterval_job_arrives_within_busy_interval_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN BusyInterval_not_quiet_implies_exists_pending_job_correspondence". exact Logic.I. Qed.
Print Assumptions BusyInterval_not_quiet_implies_exists_pending_job_correspondence.
Goal Logic.True. idtac "AUDIT_END BusyInterval_not_quiet_implies_exists_pending_job_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN BusyInterval_not_quiet_implies_not_idle_correspondence". exact Logic.I. Qed.
Print Assumptions BusyInterval_not_quiet_implies_not_idle_correspondence.
Goal Logic.True. idtac "AUDIT_END BusyInterval_not_quiet_implies_not_idle_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN BusyInterval_not_quiet_implies_exists_scheduled_hp_job_correspondence". exact Logic.I. Qed.
Print Assumptions BusyInterval_not_quiet_implies_exists_scheduled_hp_job_correspondence.
Goal Logic.True. idtac "AUDIT_END BusyInterval_not_quiet_implies_exists_scheduled_hp_job_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN BusyInterval_exists_busy_interval_prefix_correspondence". exact Logic.I. Qed.
Print Assumptions BusyInterval_exists_busy_interval_prefix_correspondence.
Goal Logic.True. idtac "AUDIT_END BusyInterval_exists_busy_interval_prefix_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN BusyInterval_busy_interval_has_uninterrupted_service_correspondence". exact Logic.I. Qed.
Print Assumptions BusyInterval_busy_interval_has_uninterrupted_service_correspondence.
Goal Logic.True. idtac "AUDIT_END BusyInterval_busy_interval_has_uninterrupted_service_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN BusyInterval_busy_interval_too_much_workload_correspondence". exact Logic.I. Qed.
Print Assumptions BusyInterval_busy_interval_too_much_workload_correspondence.
Goal Logic.True. idtac "AUDIT_END BusyInterval_busy_interval_too_much_workload_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN BusyInterval_busy_interval_workload_larger_than_interval_correspondence". exact Logic.I. Qed.
Print Assumptions BusyInterval_busy_interval_workload_larger_than_interval_correspondence.
Goal Logic.True. idtac "AUDIT_END BusyInterval_busy_interval_workload_larger_than_interval_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN BusyInterval_busy_interval_is_bounded_correspondence". exact Logic.I. Qed.
Print Assumptions BusyInterval_busy_interval_is_bounded_correspondence.
Goal Logic.True. idtac "AUDIT_END BusyInterval_busy_interval_is_bounded_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN BusyInterval_exists_busy_interval_correspondence". exact Logic.I. Qed.
Print Assumptions BusyInterval_exists_busy_interval_correspondence.
Goal Logic.True. idtac "AUDIT_END BusyInterval_exists_busy_interval_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN BusyInterval_busy_interval_bounds_response_time_correspondence". exact Logic.I. Qed.
Print Assumptions BusyInterval_busy_interval_bounds_response_time_correspondence.
Goal Logic.True. idtac "AUDIT_END BusyInterval_busy_interval_bounds_response_time_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cbi_forall_sched". exact Logic.I. Qed.
Print Assumptions cbi_forall_sched.
Goal Logic.True. idtac "AUDIT_END cbi_forall_sched". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cbi_forall_arr". exact Logic.I. Qed.
Print Assumptions cbi_forall_arr.
Goal Logic.True. idtac "AUDIT_END cbi_forall_arr". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cbi_forall_par". exact Logic.I. Qed.
Print Assumptions cbi_forall_par.
Goal Logic.True. idtac "AUDIT_END cbi_forall_par". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cbi_forall_rel". exact Logic.I. Qed.
Print Assumptions cbi_forall_rel.
Goal Logic.True. idtac "AUDIT_END cbi_forall_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cbi_service_of_hep_jobs". exact Logic.I. Qed.
Print Assumptions cbi_service_of_hep_jobs.
Goal Logic.True. idtac "AUDIT_END cbi_service_of_hep_jobs". exact Logic.I. Qed.
