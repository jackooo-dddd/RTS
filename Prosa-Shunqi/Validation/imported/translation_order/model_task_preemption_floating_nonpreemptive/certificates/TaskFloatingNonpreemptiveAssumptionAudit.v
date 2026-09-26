From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence LimitedPreemptiveCorrespondence TaskPreemptionParametersCorrespondence TaskFloatingNonpreemptiveCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN job_respects_task_max_np_segment_correspondence". exact Logic.I. Qed.
Print Assumptions job_respects_task_max_np_segment_correspondence.
Goal Logic.True. idtac "AUDIT_END job_respects_task_max_np_segment_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN valid_model_with_floating_nonpreemptive_regions_correspondence". exact Logic.I. Qed.
Print Assumptions valid_model_with_floating_nonpreemptive_regions_correspondence.
Goal Logic.True. idtac "AUDIT_END valid_model_with_floating_nonpreemptive_regions_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN tfn_floating_preemptive_rtc_threshold_related". exact Logic.I. Qed.
Print Assumptions tfn_floating_preemptive_rtc_threshold_related.
Goal Logic.True. idtac "AUDIT_END tfn_floating_preemptive_rtc_threshold_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN tfn_limited_model_related". exact Logic.I. Qed.
Print Assumptions tfn_limited_model_related.
Goal Logic.True. idtac "AUDIT_END tfn_limited_model_related". exact Logic.I. Qed.
