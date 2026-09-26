From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence CarryInCorrespondence FactsQuietTimeCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN zero_is_quiet_time_correspondence". exact Logic.I. Qed.
Print Assumptions zero_is_quiet_time_correspondence.
Goal Logic.True. idtac "AUDIT_END zero_is_quiet_time_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN no_carry_in_implies_quiet_time_correspondence". exact Logic.I. Qed.
Print Assumptions no_carry_in_implies_quiet_time_correspondence.
Goal Logic.True. idtac "AUDIT_END no_carry_in_implies_quiet_time_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN busy_interval_prefix_no_quiet_time_correspondence". exact Logic.I. Qed.
Print Assumptions busy_interval_prefix_no_quiet_time_correspondence.
Goal Logic.True. idtac "AUDIT_END busy_interval_prefix_no_quiet_time_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN busy_interval_no_quiet_time_correspondence". exact Logic.I. Qed.
Print Assumptions busy_interval_no_quiet_time_correspondence.
Goal Logic.True. idtac "AUDIT_END busy_interval_no_quiet_time_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fqt_false_correspondence". exact Logic.I. Qed.
Print Assumptions fqt_false_correspondence.
Goal Logic.True. idtac "AUDIT_END fqt_false_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fqt_not_correspondence". exact Logic.I. Qed.
Print Assumptions fqt_not_correspondence.
Goal Logic.True. idtac "AUDIT_END fqt_not_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fqt_quiet_time_related". exact Logic.I. Qed.
Print Assumptions fqt_quiet_time_related.
Goal Logic.True. idtac "AUDIT_END fqt_quiet_time_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fqt_window_related". exact Logic.I. Qed.
Print Assumptions fqt_window_related.
Goal Logic.True. idtac "AUDIT_END fqt_window_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fqt_busy_interval_prefix_related". exact Logic.I. Qed.
Print Assumptions fqt_busy_interval_prefix_related.
Goal Logic.True. idtac "AUDIT_END fqt_busy_interval_prefix_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fqt_busy_interval_related". exact Logic.I. Qed.
Print Assumptions fqt_busy_interval_related.
Goal Logic.True. idtac "AUDIT_END fqt_busy_interval_related". exact Logic.I. Qed.
