From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence TaskPreemptionParametersCorrespondence TaskPreemptionFullyNonpreemptiveCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN fully_nonpreemptive_task_model_correspondence". exact Logic.I. Qed.
Print Assumptions fully_nonpreemptive_task_model_correspondence.
Goal Logic.True. idtac "AUDIT_END fully_nonpreemptive_task_model_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN tpfn_fully_nonpreemptive_rtc_threshold_related". exact Logic.I. Qed.
Print Assumptions tpfn_fully_nonpreemptive_rtc_threshold_related.
Goal Logic.True. idtac "AUDIT_END tpfn_fully_nonpreemptive_rtc_threshold_related". exact Logic.I. Qed.
