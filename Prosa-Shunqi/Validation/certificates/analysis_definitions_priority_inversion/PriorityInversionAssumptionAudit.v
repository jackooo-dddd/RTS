From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence PriorityInversionCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN priority_inversion_correspondence". exact Logic.I. Qed.
Print Assumptions priority_inversion_correspondence.
Goal Logic.True. idtac "AUDIT_END priority_inversion_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN priority_inversion_cond_correspondence". exact Logic.I. Qed.
Print Assumptions priority_inversion_cond_correspondence.
Goal Logic.True. idtac "AUDIT_END priority_inversion_cond_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cumulative_priority_inversion_correspondence". exact Logic.I. Qed.
Print Assumptions cumulative_priority_inversion_correspondence.
Goal Logic.True. idtac "AUDIT_END cumulative_priority_inversion_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cumulative_priority_inversion_cond_correspondence". exact Logic.I. Qed.
Print Assumptions cumulative_priority_inversion_cond_correspondence.
Goal Logic.True. idtac "AUDIT_END cumulative_priority_inversion_cond_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN priority_inversion_of_job_is_bounded_by_correspondence". exact Logic.I. Qed.
Print Assumptions priority_inversion_of_job_is_bounded_by_correspondence.
Goal Logic.True. idtac "AUDIT_END priority_inversion_of_job_is_bounded_by_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN priority_inversion_of_job_cond_is_bounded_by_correspondence". exact Logic.I. Qed.
Print Assumptions priority_inversion_of_job_cond_is_bounded_by_correspondence.
Goal Logic.True. idtac "AUDIT_END priority_inversion_of_job_cond_is_bounded_by_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN priority_inversion_is_bounded_by_correspondence". exact Logic.I. Qed.
Print Assumptions priority_inversion_is_bounded_by_correspondence.
Goal Logic.True. idtac "AUDIT_END priority_inversion_is_bounded_by_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN priority_inversion_cond_is_bounded_by_correspondence". exact Logic.I. Qed.
Print Assumptions priority_inversion_cond_is_bounded_by_correspondence.
Goal Logic.True. idtac "AUDIT_END priority_inversion_cond_is_bounded_by_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pi_logic_eq_to_lean_eq". exact Logic.I. Qed.
Print Assumptions pi_logic_eq_to_lean_eq.
Goal Logic.True. idtac "AUDIT_END pi_logic_eq_to_lean_eq". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pi_lean_transport". exact Logic.I. Qed.
Print Assumptions pi_lean_transport.
Goal Logic.True. idtac "AUDIT_END pi_lean_transport". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pi_false_correspondence". exact Logic.I. Qed.
Print Assumptions pi_false_correspondence.
Goal Logic.True. idtac "AUDIT_END pi_false_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pi_not_correspondence". exact Logic.I. Qed.
Print Assumptions pi_not_correspondence.
Goal Logic.True. idtac "AUDIT_END pi_not_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pi_bool_or_related". exact Logic.I. Qed.
Print Assumptions pi_bool_or_related.
Goal Logic.True. idtac "AUDIT_END pi_bool_or_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pi_has_canonical". exact Logic.I. Qed.
Print Assumptions pi_has_canonical.
Goal Logic.True. idtac "AUDIT_END pi_has_canonical". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pi_has_related". exact Logic.I. Qed.
Print Assumptions pi_has_related.
Goal Logic.True. idtac "AUDIT_END pi_has_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pi_bool_to_nat_related". exact Logic.I. Qed.
Print Assumptions pi_bool_to_nat_related.
Goal Logic.True. idtac "AUDIT_END pi_bool_to_nat_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pi_scheduled_jobs_at_related". exact Logic.I. Qed.
Print Assumptions pi_scheduled_jobs_at_related.
Goal Logic.True. idtac "AUDIT_END pi_scheduled_jobs_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pi_quiet_time_related". exact Logic.I. Qed.
Print Assumptions pi_quiet_time_related.
Goal Logic.True. idtac "AUDIT_END pi_quiet_time_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pi_busy_interval_prefix_related". exact Logic.I. Qed.
Print Assumptions pi_busy_interval_prefix_related.
Goal Logic.True. idtac "AUDIT_END pi_busy_interval_prefix_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pi_decide_eq_related". exact Logic.I. Qed.
Print Assumptions pi_decide_eq_related.
Goal Logic.True. idtac "AUDIT_END pi_decide_eq_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pi_job_of_task_related". exact Logic.I. Qed.
Print Assumptions pi_job_of_task_related.
Goal Logic.True. idtac "AUDIT_END pi_job_of_task_related". exact Logic.I. Qed.
