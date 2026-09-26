From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations SequentialityCorrespondence
  ReadinessSequentialCorrespondence.

Goal Logic.True. idtac "AUDIT_BEGIN sequential_ready_field_correspondence". exact Logic.I. Qed.
Print Assumptions sequential_ready_field_correspondence.
Goal Logic.True. idtac "AUDIT_END sequential_ready_field_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sequential_ready_law_statement_correspondence". exact Logic.I. Qed.
Print Assumptions sequential_ready_law_statement_correspondence.
Goal Logic.True. idtac "AUDIT_END sequential_ready_law_statement_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rs_pending_related". exact Logic.I. Qed.
Print Assumptions rs_pending_related.
Goal Logic.True. idtac "AUDIT_END rs_pending_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rs_bool_implication_correspondence". exact Logic.I. Qed.
Print Assumptions rs_bool_implication_correspondence.
Goal Logic.True. idtac "AUDIT_END rs_bool_implication_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN prior_jobs_complete_correspondence". exact Logic.I. Qed.
Print Assumptions prior_jobs_complete_correspondence.
Goal Logic.True. idtac "AUDIT_END prior_jobs_complete_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sq_completed_by_related". exact Logic.I. Qed.
Print Assumptions sq_completed_by_related.
Goal Logic.True. idtac "AUDIT_END sq_completed_by_related". exact Logic.I. Qed.
