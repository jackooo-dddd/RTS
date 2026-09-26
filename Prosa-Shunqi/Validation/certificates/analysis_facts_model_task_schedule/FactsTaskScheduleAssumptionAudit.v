From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PStateCover FactsTaskScheduleCorrespondence.

Goal Logic.True. idtac "AUDIT_BEGIN task_served_task_scheduled_correspondence". exact Logic.I. Qed.
Print Assumptions task_served_task_scheduled_correspondence.
Goal Logic.True. idtac "AUDIT_END task_served_task_scheduled_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN task_served_eq_task_scheduled_correspondence". exact Logic.I. Qed.
Print Assumptions task_served_eq_task_scheduled_correspondence.
Goal Logic.True. idtac "AUDIT_END task_served_eq_task_scheduled_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN no_task_scheduled_when_idle_correspondence". exact Logic.I. Qed.
Print Assumptions no_task_scheduled_when_idle_correspondence.
Goal Logic.True. idtac "AUDIT_END no_task_scheduled_when_idle_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN no_task_served_when_idle_correspondence". exact Logic.I. Qed.
Print Assumptions no_task_served_when_idle_correspondence.
Goal Logic.True. idtac "AUDIT_END no_task_served_when_idle_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_of_scheduled_task_correspondence". exact Logic.I. Qed.
Print Assumptions job_of_scheduled_task_correspondence.
Goal Logic.True. idtac "AUDIT_END job_of_scheduled_task_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_of_task_scheduled_correspondence". exact Logic.I. Qed.
Print Assumptions job_of_task_scheduled_correspondence.
Goal Logic.True. idtac "AUDIT_END job_of_task_scheduled_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_of_other_task_scheduled_correspondence". exact Logic.I. Qed.
Print Assumptions job_of_other_task_scheduled_correspondence.
Goal Logic.True. idtac "AUDIT_END job_of_other_task_scheduled_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_of_other_task_scheduled'_correspondence". exact Logic.I. Qed.
Print Assumptions job_of_other_task_scheduled'_correspondence.
Goal Logic.True. idtac "AUDIT_END job_of_other_task_scheduled'_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_of_task_not_served_correspondence". exact Logic.I. Qed.
Print Assumptions job_of_task_not_served_correspondence.
Goal Logic.True. idtac "AUDIT_END job_of_task_not_served_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN task_served_at_eq_job_of_task_correspondence". exact Logic.I. Qed.
Print Assumptions task_served_at_eq_job_of_task_correspondence.
Goal Logic.True. idtac "AUDIT_END task_served_at_eq_job_of_task_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fts_decide_eq_related". exact Logic.I. Qed.
Print Assumptions fts_decide_eq_related.
Goal Logic.True. idtac "AUDIT_END fts_decide_eq_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fts_bool_eq_correspondence". exact Logic.I. Qed.
Print Assumptions fts_bool_eq_correspondence.
Goal Logic.True. idtac "AUDIT_END fts_bool_eq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fts_nil_eq_isEmpty_related". exact Logic.I. Qed.
Print Assumptions fts_nil_eq_isEmpty_related.
Goal Logic.True. idtac "AUDIT_END fts_nil_eq_isEmpty_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fts_job_of_task_related". exact Logic.I. Qed.
Print Assumptions fts_job_of_task_related.
Goal Logic.True. idtac "AUDIT_END fts_job_of_task_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fts_receives_service_related". exact Logic.I. Qed.
Print Assumptions fts_receives_service_related.
Goal Logic.True. idtac "AUDIT_END fts_receives_service_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fts_scheduled_jobs_of_task_related". exact Logic.I. Qed.
Print Assumptions fts_scheduled_jobs_of_task_related.
Goal Logic.True. idtac "AUDIT_END fts_scheduled_jobs_of_task_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fts_task_scheduled_at_related". exact Logic.I. Qed.
Print Assumptions fts_task_scheduled_at_related.
Goal Logic.True. idtac "AUDIT_END fts_task_scheduled_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fts_served_jobs_of_task_related". exact Logic.I. Qed.
Print Assumptions fts_served_jobs_of_task_related.
Goal Logic.True. idtac "AUDIT_END fts_served_jobs_of_task_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fts_task_served_at_related". exact Logic.I. Qed.
Print Assumptions fts_task_served_at_related.
Goal Logic.True. idtac "AUDIT_END fts_task_served_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fts_psr_supply_at_related". exact Logic.I. Qed.
Print Assumptions fts_psr_supply_at_related.
Goal Logic.True. idtac "AUDIT_END fts_psr_supply_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fts_psr_has_supply_related". exact Logic.I. Qed.
Print Assumptions fts_psr_has_supply_related.
Goal Logic.True. idtac "AUDIT_END fts_psr_has_supply_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fts_psr_fully_consuming_related". exact Logic.I. Qed.
Print Assumptions fts_psr_fully_consuming_related.
Goal Logic.True. idtac "AUDIT_END fts_psr_fully_consuming_related". exact Logic.I. Qed.
