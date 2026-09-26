From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence TaskPreemptionParametersCorrespondence TaskPreemptionFullyPreemptiveCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN fully_preemptive_task_model_correspondence". exact Logic.I. Qed.
Print Assumptions fully_preemptive_task_model_correspondence.
Goal Logic.True. idtac "AUDIT_END fully_preemptive_task_model_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN tpfp_fully_preemptive_rtc_threshold_related". exact Logic.I. Qed.
Print Assumptions tpfp_fully_preemptive_rtc_threshold_related.
Goal Logic.True. idtac "AUDIT_END tpfp_fully_preemptive_rtc_threshold_related". exact Logic.I. Qed.
