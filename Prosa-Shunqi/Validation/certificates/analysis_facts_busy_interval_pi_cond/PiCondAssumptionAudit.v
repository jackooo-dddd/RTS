From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence PreemptionTimeCorrespondence PriorityDrivenCorrespondence PStateCoverHelpers FactsPreemptionHelpers WorkloadCorrespondence PriorityInversionCorrespondence ExistenceHelpers HepAtPtHelpers TaskPreemptionParametersCorrespondence BusyIntervalPiHelpers PiCondCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN cum_task_pi_eq_correspondence". exact Logic.I. Qed.
Print Assumptions cum_task_pi_eq_correspondence.
Goal Logic.True. idtac "AUDIT_END cum_task_pi_eq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pc_forall_pred". exact Logic.I. Qed.
Print Assumptions pc_forall_pred.
Goal Logic.True. idtac "AUDIT_END pc_forall_pred". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pc_priority_inversion_cond_related". exact Logic.I. Qed.
Print Assumptions pc_priority_inversion_cond_related.
Goal Logic.True. idtac "AUDIT_END pc_priority_inversion_cond_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pc_cumulative_priority_inversion_cond_related". exact Logic.I. Qed.
Print Assumptions pc_cumulative_priority_inversion_cond_related.
Goal Logic.True. idtac "AUDIT_END pc_cumulative_priority_inversion_cond_related". exact Logic.I. Qed.
