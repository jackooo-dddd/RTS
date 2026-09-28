From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations SequentialityCorrespondence ReadinessCorrespondence FactsReadinessSequentialHelpers FactsModelSequentialCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN scheduler_executes_job_with_earliest_arrival_correspondence". exact Logic.I. Qed.
Print Assumptions scheduler_executes_job_with_earliest_arrival_correspondence.
Goal Logic.True. idtac "AUDIT_END scheduler_executes_job_with_earliest_arrival_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sequential_tasks_different_tasks_correspondence". exact Logic.I. Qed.
Print Assumptions sequential_tasks_different_tasks_correspondence.
Goal Logic.True. idtac "AUDIT_END sequential_tasks_different_tasks_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sequential_tasks_from_readiness_correspondence". exact Logic.I. Qed.
Print Assumptions sequential_tasks_from_readiness_correspondence.
Goal Logic.True. idtac "AUDIT_END sequential_tasks_from_readiness_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fms_and_true_intro". exact Logic.I. Qed.
Print Assumptions fms_and_true_intro.
Goal Logic.True. idtac "AUDIT_END fms_and_true_intro". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fms_and_true_right". exact Logic.I. Qed.
Print Assumptions fms_and_true_right.
Goal Logic.True. idtac "AUDIT_END fms_and_true_right". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fms_canonical_rel". exact Logic.I. Qed.
Print Assumptions fms_canonical_rel.
Goal Logic.True. idtac "AUDIT_END fms_canonical_rel". exact Logic.I. Qed.
