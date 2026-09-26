From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence TaskPreemptionParametersCorrespondence TaskPreemptionFullyNonpreemptiveCorrespondence FactsRtcNonpreemptiveCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN job_rtc_threshold_is_0_correspondence". exact Logic.I. Qed.
Print Assumptions job_rtc_threshold_is_0_correspondence.
Goal Logic.True. idtac "AUDIT_END job_rtc_threshold_is_0_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_rtc_threshold_is_ε_correspondence". exact Logic.I. Qed.
Print Assumptions job_rtc_threshold_is_ε_correspondence.
Goal Logic.True. idtac "AUDIT_END job_rtc_threshold_is_ε_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fully_nonpreemptive_valid_task_run_to_completion_threshold_correspondence". exact Logic.I. Qed.
Print Assumptions fully_nonpreemptive_valid_task_run_to_completion_threshold_correspondence.
Goal Logic.True. idtac "AUDIT_END fully_nonpreemptive_valid_task_run_to_completion_threshold_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frnp_lean_transport". exact Logic.I. Qed.
Print Assumptions frnp_lean_transport.
Goal Logic.True. idtac "AUDIT_END frnp_lean_transport". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frnp_fully_nonpreemptive_job_related". exact Logic.I. Qed.
Print Assumptions frnp_fully_nonpreemptive_job_related.
Goal Logic.True. idtac "AUDIT_END frnp_fully_nonpreemptive_job_related". exact Logic.I. Qed.
