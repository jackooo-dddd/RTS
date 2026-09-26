From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence PreemptionTimeCorrespondence PriorityDrivenCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN respects_JLDP_policy_at_preemption_point_correspondence". exact Logic.I. Qed.
Print Assumptions respects_JLDP_policy_at_preemption_point_correspondence.
Goal Logic.True. idtac "AUDIT_END respects_JLDP_policy_at_preemption_point_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN respects_JLFP_policy_at_preemption_point_correspondence". exact Logic.I. Qed.
Print Assumptions respects_JLFP_policy_at_preemption_point_correspondence.
Goal Logic.True. idtac "AUDIT_END respects_JLFP_policy_at_preemption_point_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN respects_FP_policy_at_preemption_point_correspondence". exact Logic.I. Qed.
Print Assumptions respects_FP_policy_at_preemption_point_correspondence.
Goal Logic.True. idtac "AUDIT_END respects_FP_policy_at_preemption_point_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pdrv_backlogged_related". exact Logic.I. Qed.
Print Assumptions pdrv_backlogged_related.
Goal Logic.True. idtac "AUDIT_END pdrv_backlogged_related". exact Logic.I. Qed.
