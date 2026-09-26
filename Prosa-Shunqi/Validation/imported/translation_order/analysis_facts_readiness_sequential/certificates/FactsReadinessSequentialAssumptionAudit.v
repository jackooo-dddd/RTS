From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations SequentialityCorrespondence ReadinessCorrespondence FactsReadinessSequentialCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN sequential_readiness_is_sequential_correspondence". exact Logic.I. Qed.
Print Assumptions sequential_readiness_is_sequential_correspondence.
Goal Logic.True. idtac "AUDIT_END sequential_readiness_is_sequential_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sequential_readiness_nonclairvoyance_correspondence". exact Logic.I. Qed.
Print Assumptions sequential_readiness_nonclairvoyance_correspondence.
Goal Logic.True. idtac "AUDIT_END sequential_readiness_nonclairvoyance_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sequential_readiness_implies_sequential_tasks_correspondence". exact Logic.I. Qed.
Print Assumptions sequential_readiness_implies_sequential_tasks_correspondence.
Goal Logic.True. idtac "AUDIT_END sequential_readiness_implies_sequential_tasks_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sequential_readiness_implies_work_bearing_readiness_correspondence". exact Logic.I. Qed.
Print Assumptions sequential_readiness_implies_work_bearing_readiness_correspondence.
Goal Logic.True. idtac "AUDIT_END sequential_readiness_implies_work_bearing_readiness_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frs_exists_identity". exact Logic.I. Qed.
Print Assumptions frs_exists_identity.
Goal Logic.True. idtac "AUDIT_END frs_exists_identity". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frs_scheduled_at_related". exact Logic.I. Qed.
Print Assumptions frs_scheduled_at_related.
Goal Logic.True. idtac "AUDIT_END frs_scheduled_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frs_pending_related". exact Logic.I. Qed.
Print Assumptions frs_pending_related.
Goal Logic.True. idtac "AUDIT_END frs_pending_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frs_sequential_instance_related". exact Logic.I. Qed.
Print Assumptions frs_sequential_instance_related.
Goal Logic.True. idtac "AUDIT_END frs_sequential_instance_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frs_forall_schedule". exact Logic.I. Qed.
Print Assumptions frs_forall_schedule.
Goal Logic.True. idtac "AUDIT_END frs_forall_schedule". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frs_fp_to_target_rel". exact Logic.I. Qed.
Print Assumptions frs_fp_to_target_rel.
Goal Logic.True. idtac "AUDIT_END frs_fp_to_target_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frs_fp_to_source_rel". exact Logic.I. Qed.
Print Assumptions frs_fp_to_source_rel.
Goal Logic.True. idtac "AUDIT_END frs_fp_to_source_rel". exact Logic.I. Qed.
