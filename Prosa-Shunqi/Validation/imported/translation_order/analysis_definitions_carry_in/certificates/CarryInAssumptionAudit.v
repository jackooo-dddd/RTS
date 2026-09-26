From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations CarryInCorrespondence.

Goal Logic.True. idtac "AUDIT_BEGIN no_carry_in_correspondence". exact Logic.I. Qed.
Print Assumptions no_carry_in_correspondence.
Goal Logic.True. idtac "AUDIT_END no_carry_in_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ci_completed_by_related". exact Logic.I. Qed.
Print Assumptions ci_completed_by_related.
Goal Logic.True. idtac "AUDIT_END ci_completed_by_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ci_service_related". exact Logic.I. Qed.
Print Assumptions ci_service_related.
Goal Logic.True. idtac "AUDIT_END ci_service_related". exact Logic.I. Qed.
