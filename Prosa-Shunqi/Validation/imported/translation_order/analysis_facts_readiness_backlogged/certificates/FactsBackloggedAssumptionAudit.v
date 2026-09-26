From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations SequentialityCorrespondence ReadinessCorrespondence FactsBackloggedCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN mem_backlogged_jobs_correspondence". exact Logic.I. Qed.
Print Assumptions mem_backlogged_jobs_correspondence.
Goal Logic.True. idtac "AUDIT_END mem_backlogged_jobs_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN backlogged_job_arrives_in_correspondence". exact Logic.I. Qed.
Print Assumptions backlogged_job_arrives_in_correspondence.
Goal Logic.True. idtac "AUDIT_END backlogged_job_arrives_in_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN backlogged_prefix_invariance_correspondence". exact Logic.I. Qed.
Print Assumptions backlogged_prefix_invariance_correspondence.
Goal Logic.True. idtac "AUDIT_END backlogged_prefix_invariance_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN backlogged_prefix_invariance'_correspondence". exact Logic.I. Qed.
Print Assumptions backlogged_prefix_invariance'_correspondence.
Goal Logic.True. idtac "AUDIT_END backlogged_prefix_invariance'_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN backlogged_jobs_prefix_invariance_correspondence". exact Logic.I. Qed.
Print Assumptions backlogged_jobs_prefix_invariance_correspondence.
Goal Logic.True. idtac "AUDIT_END backlogged_jobs_prefix_invariance_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fbl_arrival_sequence_to_source_rel". exact Logic.I. Qed.
Print Assumptions fbl_arrival_sequence_to_source_rel.
Goal Logic.True. idtac "AUDIT_END fbl_arrival_sequence_to_source_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fbl_scheduled_at_related". exact Logic.I. Qed.
Print Assumptions fbl_scheduled_at_related.
Goal Logic.True. idtac "AUDIT_END fbl_scheduled_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fbl_backlogged_related". exact Logic.I. Qed.
Print Assumptions fbl_backlogged_related.
Goal Logic.True. idtac "AUDIT_END fbl_backlogged_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fbl_jobs_backlogged_at_related". exact Logic.I. Qed.
Print Assumptions fbl_jobs_backlogged_at_related.
Goal Logic.True. idtac "AUDIT_END fbl_jobs_backlogged_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fbl_forall_schedule". exact Logic.I. Qed.
Print Assumptions fbl_forall_schedule.
Goal Logic.True. idtac "AUDIT_END fbl_forall_schedule". exact Logic.I. Qed.
