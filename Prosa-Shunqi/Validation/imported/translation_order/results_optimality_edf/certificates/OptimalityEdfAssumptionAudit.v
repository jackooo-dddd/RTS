From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence IdealUniSchedulerCorrespondence EdfDefinitionsHelpers EdfTransCorrespondence FactsEdfOptCorrespondence OptimalityEdfCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN EDF_optimality_correspondence". exact Logic.I. Qed.
Print Assumptions EDF_optimality_correspondence.
Goal Logic.True. idtac "AUDIT_END EDF_optimality_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN EDF_WC_optimality_correspondence". exact Logic.I. Qed.
Print Assumptions EDF_WC_optimality_correspondence.
Goal Logic.True. idtac "AUDIT_END EDF_WC_optimality_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN EDF_priority_compliant_WC_optimality_correspondence". exact Logic.I. Qed.
Print Assumptions EDF_priority_compliant_WC_optimality_correspondence.
Goal Logic.True. idtac "AUDIT_END EDF_priority_compliant_WC_optimality_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN weak_EDF_optimality_correspondence". exact Logic.I. Qed.
Print Assumptions weak_EDF_optimality_correspondence.
Goal Logic.True. idtac "AUDIT_END weak_EDF_optimality_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN oed_ready_related". exact Logic.I. Qed.
Print Assumptions oed_ready_related.
Goal Logic.True. idtac "AUDIT_END oed_ready_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN oed_preemptable_related". exact Logic.I. Qed.
Print Assumptions oed_preemptable_related.
Goal Logic.True. idtac "AUDIT_END oed_preemptable_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN oed_exists_sched". exact Logic.I. Qed.
Print Assumptions oed_exists_sched.
Goal Logic.True. idtac "AUDIT_END oed_exists_sched". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN oed_sched_at". exact Logic.I. Qed.
Print Assumptions oed_sched_at.
Goal Logic.True. idtac "AUDIT_END oed_sched_at". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN oed_wc_rel". exact Logic.I. Qed.
Print Assumptions oed_wc_rel.
Goal Logic.True. idtac "AUDIT_END oed_wc_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN oed_respects_rel". exact Logic.I. Qed.
Print Assumptions oed_respects_rel.
Goal Logic.True. idtac "AUDIT_END oed_respects_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN oed_premise". exact Logic.I. Qed.
Print Assumptions oed_premise.
Goal Logic.True. idtac "AUDIT_END oed_premise". exact Logic.I. Qed.
