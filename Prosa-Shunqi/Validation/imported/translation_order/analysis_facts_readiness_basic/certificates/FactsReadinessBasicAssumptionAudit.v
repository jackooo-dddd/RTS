From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations SequentialityCorrespondence ReadinessCorrespondence FactsReadinessBasicCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN basic_readiness_nonclairvoyance_correspondence". exact Logic.I. Qed.
Print Assumptions basic_readiness_nonclairvoyance_correspondence.
Goal Logic.True. idtac "AUDIT_END basic_readiness_nonclairvoyance_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN basic_readiness_compliance_correspondence". exact Logic.I. Qed.
Print Assumptions basic_readiness_compliance_correspondence.
Goal Logic.True. idtac "AUDIT_END basic_readiness_compliance_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN basic_readiness_is_work_bearing_readiness_correspondence". exact Logic.I. Qed.
Print Assumptions basic_readiness_is_work_bearing_readiness_correspondence.
Goal Logic.True. idtac "AUDIT_END basic_readiness_is_work_bearing_readiness_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frb_scheduled_at_related". exact Logic.I. Qed.
Print Assumptions frb_scheduled_at_related.
Goal Logic.True. idtac "AUDIT_END frb_scheduled_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frb_completed_by_related". exact Logic.I. Qed.
Print Assumptions frb_completed_by_related.
Goal Logic.True. idtac "AUDIT_END frb_completed_by_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frb_pending_related". exact Logic.I. Qed.
Print Assumptions frb_pending_related.
Goal Logic.True. idtac "AUDIT_END frb_pending_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frb_basic_ready_related". exact Logic.I. Qed.
Print Assumptions frb_basic_ready_related.
Goal Logic.True. idtac "AUDIT_END frb_basic_ready_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frb_exists_identity". exact Logic.I. Qed.
Print Assumptions frb_exists_identity.
Goal Logic.True. idtac "AUDIT_END frb_exists_identity". exact Logic.I. Qed.
