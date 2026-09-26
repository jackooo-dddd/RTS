From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations SequentialityCorrespondence.

Goal Logic.True. idtac "AUDIT_BEGIN sequential_tasks_correspondence". exact Logic.I. Qed.
Print Assumptions sequential_tasks_correspondence.
Goal Logic.True. idtac "AUDIT_END sequential_tasks_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN prior_jobs_complete_correspondence". exact Logic.I. Qed.
Print Assumptions prior_jobs_complete_correspondence.
Goal Logic.True. idtac "AUDIT_END prior_jobs_complete_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sq_all_related". exact Logic.I. Qed.
Print Assumptions sq_all_related.
Goal Logic.True. idtac "AUDIT_END sq_all_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sq_completed_by_related". exact Logic.I. Qed.
Print Assumptions sq_completed_by_related.
Goal Logic.True. idtac "AUDIT_END sq_completed_by_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sq_scheduled_at_related". exact Logic.I. Qed.
Print Assumptions sq_scheduled_at_related.
Goal Logic.True. idtac "AUDIT_END sq_scheduled_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sq_same_task_related". exact Logic.I. Qed.
Print Assumptions sq_same_task_related.
Goal Logic.True. idtac "AUDIT_END sq_same_task_related". exact Logic.I. Qed.
