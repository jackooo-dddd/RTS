From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations FactsDeadlinesCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN incomplete_implies_later_deadline_correspondence". exact Logic.I. Qed.
Print Assumptions incomplete_implies_later_deadline_correspondence.
Goal Logic.True. idtac "AUDIT_END incomplete_implies_later_deadline_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN incomplete_implies_scheduled_later_correspondence". exact Logic.I. Qed.
Print Assumptions incomplete_implies_scheduled_later_correspondence.
Goal Logic.True. idtac "AUDIT_END incomplete_implies_scheduled_later_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN scheduled_at_implies_later_deadline_correspondence". exact Logic.I. Qed.
Print Assumptions scheduled_at_implies_later_deadline_correspondence.
Goal Logic.True. idtac "AUDIT_END scheduled_at_implies_later_deadline_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_invariant_implies_deadline_met_correspondence". exact Logic.I. Qed.
Print Assumptions service_invariant_implies_deadline_met_correspondence.
Goal Logic.True. idtac "AUDIT_END service_invariant_implies_deadline_met_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fdl_iff_correspondence". exact Logic.I. Qed.
Print Assumptions fdl_iff_correspondence.
Goal Logic.True. idtac "AUDIT_END fdl_iff_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fdl_scheduled_at_related". exact Logic.I. Qed.
Print Assumptions fdl_scheduled_at_related.
Goal Logic.True. idtac "AUDIT_END fdl_scheduled_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fdl_service_at_related". exact Logic.I. Qed.
Print Assumptions fdl_service_at_related.
Goal Logic.True. idtac "AUDIT_END fdl_service_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fdl_service_related". exact Logic.I. Qed.
Print Assumptions fdl_service_related.
Goal Logic.True. idtac "AUDIT_END fdl_service_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fdl_completed_by_related". exact Logic.I. Qed.
Print Assumptions fdl_completed_by_related.
Goal Logic.True. idtac "AUDIT_END fdl_completed_by_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fdl_job_meets_deadline_related". exact Logic.I. Qed.
Print Assumptions fdl_job_meets_deadline_related.
Goal Logic.True. idtac "AUDIT_END fdl_job_meets_deadline_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fdl_completed_jobs_dont_execute_related". exact Logic.I. Qed.
Print Assumptions fdl_completed_jobs_dont_execute_related.
Goal Logic.True. idtac "AUDIT_END fdl_completed_jobs_dont_execute_related". exact Logic.I. Qed.
