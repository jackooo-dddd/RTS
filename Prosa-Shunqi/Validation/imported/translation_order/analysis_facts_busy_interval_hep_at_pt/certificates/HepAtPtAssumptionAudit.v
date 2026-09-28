From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence PreemptionTimeCorrespondence PriorityDrivenCorrespondence PStateCoverHelpers FactsPreemptionHelpers WorkloadCorrespondence PriorityInversionCorrespondence ExistenceHelpers HepAtPtCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN instant_t_is_not_idle_correspondence". exact Logic.I. Qed.
Print Assumptions instant_t_is_not_idle_correspondence.
Goal Logic.True. idtac "AUDIT_END instant_t_is_not_idle_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN scheduled_at_preemption_time_implies_higher_or_equal_priority_lt_correspondence". exact Logic.I. Qed.
Print Assumptions scheduled_at_preemption_time_implies_higher_or_equal_priority_lt_correspondence.
Goal Logic.True. idtac "AUDIT_END scheduled_at_preemption_time_implies_higher_or_equal_priority_lt_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN scheduled_at_preemption_time_implies_higher_or_equal_priority_eq_correspondence". exact Logic.I. Qed.
Print Assumptions scheduled_at_preemption_time_implies_higher_or_equal_priority_eq_correspondence.
Goal Logic.True. idtac "AUDIT_END scheduled_at_preemption_time_implies_higher_or_equal_priority_eq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN scheduled_at_preemption_time_implies_higher_or_equal_priority_correspondence". exact Logic.I. Qed.
Print Assumptions scheduled_at_preemption_time_implies_higher_or_equal_priority_correspondence.
Goal Logic.True. idtac "AUDIT_END scheduled_at_preemption_time_implies_higher_or_equal_priority_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN scheduled_at_preemption_time_implies_arrived_between_within_busy_interval_correspondence". exact Logic.I. Qed.
Print Assumptions scheduled_at_preemption_time_implies_arrived_between_within_busy_interval_correspondence.
Goal Logic.True. idtac "AUDIT_END scheduled_at_preemption_time_implies_arrived_between_within_busy_interval_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN not_quiet_implies_exists_scheduled_hp_job_at_preemption_point_correspondence". exact Logic.I. Qed.
Print Assumptions not_quiet_implies_exists_scheduled_hp_job_at_preemption_point_correspondence.
Goal Logic.True. idtac "AUDIT_END not_quiet_implies_exists_scheduled_hp_job_at_preemption_point_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN not_quiet_implies_exists_scheduled_hp_job_after_preemption_point_correspondence". exact Logic.I. Qed.
Print Assumptions not_quiet_implies_exists_scheduled_hp_job_after_preemption_point_correspondence.
Goal Logic.True. idtac "AUDIT_END not_quiet_implies_exists_scheduled_hp_job_after_preemption_point_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN not_quiet_implies_exists_scheduled_hp_job_correspondence". exact Logic.I. Qed.
Print Assumptions not_quiet_implies_exists_scheduled_hp_job_correspondence.
Goal Logic.True. idtac "AUDIT_END not_quiet_implies_exists_scheduled_hp_job_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN hap_pred_related". exact Logic.I. Qed.
Print Assumptions hap_pred_related.
Goal Logic.True. idtac "AUDIT_END hap_pred_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN hap_transitive_rel". exact Logic.I. Qed.
Print Assumptions hap_transitive_rel.
Goal Logic.True. idtac "AUDIT_END hap_transitive_rel". exact Logic.I. Qed.
