From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence ServiceInversionPredCorrespondence ServiceInversionBusyPrefixCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN service_inversion_of_job_is_bounded_by_correspondence". exact Logic.I. Qed.
Print Assumptions service_inversion_of_job_is_bounded_by_correspondence.
Goal Logic.True. idtac "AUDIT_END service_inversion_of_job_is_bounded_by_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_inversion_is_bounded_by_correspondence". exact Logic.I. Qed.
Print Assumptions service_inversion_is_bounded_by_correspondence.
Goal Logic.True. idtac "AUDIT_END service_inversion_is_bounded_by_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sibp_false_correspondence". exact Logic.I. Qed.
Print Assumptions sibp_false_correspondence.
Goal Logic.True. idtac "AUDIT_END sibp_false_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sibp_not_correspondence". exact Logic.I. Qed.
Print Assumptions sibp_not_correspondence.
Goal Logic.True. idtac "AUDIT_END sibp_not_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sibp_quiet_time_related". exact Logic.I. Qed.
Print Assumptions sibp_quiet_time_related.
Goal Logic.True. idtac "AUDIT_END sibp_quiet_time_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sibp_busy_interval_prefix_related". exact Logic.I. Qed.
Print Assumptions sibp_busy_interval_prefix_related.
Goal Logic.True. idtac "AUDIT_END sibp_busy_interval_prefix_related". exact Logic.I. Qed.
