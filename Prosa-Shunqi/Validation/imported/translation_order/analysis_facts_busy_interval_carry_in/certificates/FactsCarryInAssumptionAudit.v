From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence PreemptionTimeCorrespondence PriorityDrivenCorrespondence PStateCoverHelpers FactsPreemptionHelpers WorkloadCorrespondence PriorityInversionCorrespondence ExistenceHelpers FactsCarryInCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN no_carry_in_at_zero_correspondence". exact Logic.I. Qed.
Print Assumptions no_carry_in_at_zero_correspondence.
Goal Logic.True. idtac "AUDIT_END no_carry_in_at_zero_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pending_job_not_idle_correspondence". exact Logic.I. Qed.
Print Assumptions pending_job_not_idle_correspondence.
Goal Logic.True. idtac "AUDIT_END pending_job_not_idle_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN idle_instant_no_carry_in_correspondence". exact Logic.I. Qed.
Print Assumptions idle_instant_no_carry_in_correspondence.
Goal Logic.True. idtac "AUDIT_END idle_instant_no_carry_in_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN idle_instant_next_no_carry_in_correspondence". exact Logic.I. Qed.
Print Assumptions idle_instant_next_no_carry_in_correspondence.
Goal Logic.True. idtac "AUDIT_END idle_instant_next_no_carry_in_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN total_service_is_bounded_by_Δ_correspondence". exact Logic.I. Qed.
Print Assumptions total_service_is_bounded_by_Δ_correspondence.
Goal Logic.True. idtac "AUDIT_END total_service_is_bounded_by_Δ_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN low_total_service_implies_existence_of_time_with_no_carry_in_correspondence". exact Logic.I. Qed.
Print Assumptions low_total_service_implies_existence_of_time_with_no_carry_in_correspondence.
Goal Logic.True. idtac "AUDIT_END low_total_service_implies_existence_of_time_with_no_carry_in_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN completion_of_all_jobs_implies_no_carry_in_correspondence". exact Logic.I. Qed.
Print Assumptions completion_of_all_jobs_implies_no_carry_in_correspondence.
Goal Logic.True. idtac "AUDIT_END completion_of_all_jobs_implies_no_carry_in_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN processor_is_not_too_busy_correspondence". exact Logic.I. Qed.
Print Assumptions processor_is_not_too_busy_correspondence.
Goal Logic.True. idtac "AUDIT_END processor_is_not_too_busy_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN busy_interval_from_total_workload_bound_correspondence". exact Logic.I. Qed.
Print Assumptions busy_interval_from_total_workload_bound_correspondence.
Goal Logic.True. idtac "AUDIT_END busy_interval_from_total_workload_bound_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fci_supply_at_related". exact Logic.I. Qed.
Print Assumptions fci_supply_at_related.
Goal Logic.True. idtac "AUDIT_END fci_supply_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fci_is_blackout_related". exact Logic.I. Qed.
Print Assumptions fci_is_blackout_related.
Goal Logic.True. idtac "AUDIT_END fci_is_blackout_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fci_blackout_during_related". exact Logic.I. Qed.
Print Assumptions fci_blackout_during_related.
Goal Logic.True. idtac "AUDIT_END fci_blackout_during_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fci_no_carry_in_related". exact Logic.I. Qed.
Print Assumptions fci_no_carry_in_related.
Goal Logic.True. idtac "AUDIT_END fci_no_carry_in_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fci_total_workload_between_related". exact Logic.I. Qed.
Print Assumptions fci_total_workload_between_related.
Goal Logic.True. idtac "AUDIT_END fci_total_workload_between_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fci_fully_consuming_related". exact Logic.I. Qed.
Print Assumptions fci_fully_consuming_related.
Goal Logic.True. idtac "AUDIT_END fci_fully_consuming_related". exact Logic.I. Qed.
