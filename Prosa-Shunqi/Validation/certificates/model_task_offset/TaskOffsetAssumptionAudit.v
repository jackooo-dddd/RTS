From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence TaskOffsetCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN TaskOffset_source_total". exact Logic.I. Qed.
Print Assumptions TaskOffset_source_total.
Goal Logic.True. idtac "AUDIT_END TaskOffset_source_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN TaskOffset_target_total". exact Logic.I. Qed.
Print Assumptions TaskOffset_target_total.
Goal Logic.True. idtac "AUDIT_END TaskOffset_target_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN no_jobs_before_offset_correspondence". exact Logic.I. Qed.
Print Assumptions no_jobs_before_offset_correspondence.
Goal Logic.True. idtac "AUDIT_END no_jobs_before_offset_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_released_at_offset_correspondence". exact Logic.I. Qed.
Print Assumptions job_released_at_offset_correspondence.
Goal Logic.True. idtac "AUDIT_END job_released_at_offset_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN valid_offset_correspondence". exact Logic.I. Qed.
Print Assumptions valid_offset_correspondence.
Goal Logic.True. idtac "AUDIT_END valid_offset_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN valid_offsets_correspondence". exact Logic.I. Qed.
Print Assumptions valid_offsets_correspondence.
Goal Logic.True. idtac "AUDIT_END valid_offsets_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN task_offsets_correspondence". exact Logic.I. Qed.
Print Assumptions task_offsets_correspondence.
Goal Logic.True. idtac "AUDIT_END task_offsets_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN max_task_offset_correspondence". exact Logic.I. Qed.
Print Assumptions max_task_offset_correspondence.
Goal Logic.True. idtac "AUDIT_END max_task_offset_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN off_eq_correspondence". exact Logic.I. Qed.
Print Assumptions off_eq_correspondence.
Goal Logic.True. idtac "AUDIT_END off_eq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN off_exists_identity". exact Logic.I. Qed.
Print Assumptions off_exists_identity.
Goal Logic.True. idtac "AUDIT_END off_exists_identity". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN off_map_canonical". exact Logic.I. Qed.
Print Assumptions off_map_canonical.
Goal Logic.True. idtac "AUDIT_END off_map_canonical". exact Logic.I. Qed.
