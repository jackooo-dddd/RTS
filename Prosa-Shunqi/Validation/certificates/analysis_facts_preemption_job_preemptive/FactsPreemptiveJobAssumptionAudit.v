From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence FactsPreemptiveJobCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN valid_fully_preemptive_model_correspondence". exact Logic.I. Qed.
Print Assumptions valid_fully_preemptive_model_correspondence.
Goal Logic.True. idtac "AUDIT_END valid_fully_preemptive_model_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_max_nps_is_0_correspondence". exact Logic.I. Qed.
Print Assumptions job_max_nps_is_0_correspondence.
Goal Logic.True. idtac "AUDIT_END job_max_nps_is_0_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_max_nps_is_ε_correspondence". exact Logic.I. Qed.
Print Assumptions job_max_nps_is_ε_correspondence.
Goal Logic.True. idtac "AUDIT_END job_max_nps_is_ε_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fpj_fully_preemptive_related". exact Logic.I. Qed.
Print Assumptions fpj_fully_preemptive_related.
Goal Logic.True. idtac "AUDIT_END fpj_fully_preemptive_related". exact Logic.I. Qed.
