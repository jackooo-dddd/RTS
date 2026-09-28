From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence PreemptionTimeCorrespondence PriorityDrivenCorrespondence PStateCoverHelpers FactsPreemptionHelpers WorkloadCorrespondence PriorityInversionCorrespondence ExistenceHelpers HepAtPtHelpers TaskPreemptionParametersCorrespondence BusyIntervalPiHelpers ServiceInversionPredCorrespondence BusyIntervalServiceInversionCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN blackout_implies_no_service_inversion_correspondence". exact Logic.I. Qed.
Print Assumptions blackout_implies_no_service_inversion_correspondence.
Goal Logic.True. idtac "AUDIT_END blackout_implies_no_service_inversion_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN idle_implies_no_service_inversion_correspondence". exact Logic.I. Qed.
Print Assumptions idle_implies_no_service_inversion_correspondence.
Goal Logic.True. idtac "AUDIT_END idle_implies_no_service_inversion_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN receives_service_implies_no_service_inversion_correspondence". exact Logic.I. Qed.
Print Assumptions receives_service_implies_no_service_inversion_correspondence.
Goal Logic.True. idtac "AUDIT_END receives_service_implies_no_service_inversion_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_inversion_cat_correspondence". exact Logic.I. Qed.
Print Assumptions service_inversion_cat_correspondence.
Goal Logic.True. idtac "AUDIT_END service_inversion_cat_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_inversion_widen_correspondence". exact Logic.I. Qed.
Print Assumptions service_inversion_widen_correspondence.
Goal Logic.True. idtac "AUDIT_END service_inversion_widen_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_inversion_supply_sched_correspondence". exact Logic.I. Qed.
Print Assumptions service_inversion_supply_sched_correspondence.
Goal Logic.True. idtac "AUDIT_END service_inversion_supply_sched_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_inv_implies_priority_inv_correspondence". exact Logic.I. Qed.
Print Assumptions service_inv_implies_priority_inv_correspondence.
Goal Logic.True. idtac "AUDIT_END service_inv_implies_priority_inv_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cumul_service_inv_le_cumul_priority_inv_correspondence". exact Logic.I. Qed.
Print Assumptions cumul_service_inv_le_cumul_priority_inv_correspondence.
Goal Logic.True. idtac "AUDIT_END cumul_service_inv_le_cumul_priority_inv_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cumulative_service_inversion_from_one_job_correspondence". exact Logic.I. Qed.
Print Assumptions cumulative_service_inversion_from_one_job_correspondence.
Goal Logic.True. idtac "AUDIT_END cumulative_service_inversion_from_one_job_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN lp_job_bounded_service_correspondence". exact Logic.I. Qed.
Print Assumptions lp_job_bounded_service_correspondence.
Goal Logic.True. idtac "AUDIT_END lp_job_bounded_service_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN lp_job_bounded_service_max_correspondence". exact Logic.I. Qed.
Print Assumptions lp_job_bounded_service_max_correspondence.
Goal Logic.True. idtac "AUDIT_END lp_job_bounded_service_max_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_inversion_is_bounded_correspondence". exact Logic.I. Qed.
Print Assumptions service_inversion_is_bounded_correspondence.
Goal Logic.True. idtac "AUDIT_END service_inversion_is_bounded_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bsi_forall_jldp". exact Logic.I. Qed.
Print Assumptions bsi_forall_jldp.
Goal Logic.True. idtac "AUDIT_END bsi_forall_jldp". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bsi_reflexive_priorities_rel". exact Logic.I. Qed.
Print Assumptions bsi_reflexive_priorities_rel.
Goal Logic.True. idtac "AUDIT_END bsi_reflexive_priorities_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bsi_jlfp_to_jldp_rel". exact Logic.I. Qed.
Print Assumptions bsi_jlfp_to_jldp_rel.
Goal Logic.True. idtac "AUDIT_END bsi_jlfp_to_jldp_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bsi_unit_supply_related". exact Logic.I. Qed.
Print Assumptions bsi_unit_supply_related.
Goal Logic.True. idtac "AUDIT_END bsi_unit_supply_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bsi_supply_at_related". exact Logic.I. Qed.
Print Assumptions bsi_supply_at_related.
Goal Logic.True. idtac "AUDIT_END bsi_supply_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bsi_has_supply_related". exact Logic.I. Qed.
Print Assumptions bsi_has_supply_related.
Goal Logic.True. idtac "AUDIT_END bsi_has_supply_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bsi_is_blackout_related". exact Logic.I. Qed.
Print Assumptions bsi_is_blackout_related.
Goal Logic.True. idtac "AUDIT_END bsi_is_blackout_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bsi_receives_service_at_related". exact Logic.I. Qed.
Print Assumptions bsi_receives_service_at_related.
Goal Logic.True. idtac "AUDIT_END bsi_receives_service_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bsi_served_jobs_at_related". exact Logic.I. Qed.
Print Assumptions bsi_served_jobs_at_related.
Goal Logic.True. idtac "AUDIT_END bsi_served_jobs_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bsi_service_inversion_related". exact Logic.I. Qed.
Print Assumptions bsi_service_inversion_related.
Goal Logic.True. idtac "AUDIT_END bsi_service_inversion_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bsi_cumulative_service_inversion_related". exact Logic.I. Qed.
Print Assumptions bsi_cumulative_service_inversion_related.
Goal Logic.True. idtac "AUDIT_END bsi_cumulative_service_inversion_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bsi_fully_consuming_related". exact Logic.I. Qed.
Print Assumptions bsi_fully_consuming_related.
Goal Logic.True. idtac "AUDIT_END bsi_fully_consuming_related". exact Logic.I. Qed.
