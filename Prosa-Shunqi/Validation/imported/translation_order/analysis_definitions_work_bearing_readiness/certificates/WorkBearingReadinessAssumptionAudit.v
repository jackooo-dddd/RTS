From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations WorkBearingReadinessCorrespondence.

Goal Logic.True. idtac "AUDIT_BEGIN work_bearing_readiness_correspondence". exact Logic.I. Qed.
Print Assumptions work_bearing_readiness_correspondence.
Goal Logic.True. idtac "AUDIT_END work_bearing_readiness_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wb_pending_related". exact Logic.I. Qed.
Print Assumptions wb_pending_related.
Goal Logic.True. idtac "AUDIT_END wb_pending_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wb_exists_identity". exact Logic.I. Qed.
Print Assumptions wb_exists_identity.
Goal Logic.True. idtac "AUDIT_END wb_exists_identity". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN JLFP_policy_source_total". exact Logic.I. Qed.
Print Assumptions JLFP_policy_source_total.
Goal Logic.True. idtac "AUDIT_END JLFP_policy_source_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN JLFP_policy_target_total". exact Logic.I. Qed.
Print Assumptions JLFP_policy_target_total.
Goal Logic.True. idtac "AUDIT_END JLFP_policy_target_total". exact Logic.I. Qed.
