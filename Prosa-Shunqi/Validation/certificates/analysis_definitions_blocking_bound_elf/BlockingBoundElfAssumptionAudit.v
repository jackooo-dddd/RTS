From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence TaskPreemptionParametersCorrespondence NatSubCorrespondence PcoBaseAdapter PcoStaticOrder PcoDynamicOrder PriorityCoercionCorrespondence PriorityGelHelpers BlockingBoundElfCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN blocking_bound_correspondence". exact Logic.I. Qed.
Print Assumptions blocking_bound_correspondence.
Goal Logic.True. idtac "AUDIT_END blocking_bound_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbelf_bigmax_canonical". exact Logic.I. Qed.
Print Assumptions bbelf_bigmax_canonical.
Goal Logic.True. idtac "AUDIT_END bbelf_bigmax_canonical". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbelf_bigmax_related". exact Logic.I. Qed.
Print Assumptions bbelf_bigmax_related.
Goal Logic.True. idtac "AUDIT_END bbelf_bigmax_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbelf_hp_task_related". exact Logic.I. Qed.
Print Assumptions bbelf_hp_task_related.
Goal Logic.True. idtac "AUDIT_END bbelf_hp_task_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbelf_ep_task_related". exact Logic.I. Qed.
Print Assumptions bbelf_ep_task_related.
Goal Logic.True. idtac "AUDIT_END bbelf_ep_task_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbelf_point_lt_related". exact Logic.I. Qed.
Print Assumptions bbelf_point_lt_related.
Goal Logic.True. idtac "AUDIT_END bbelf_point_lt_related". exact Logic.I. Qed.
