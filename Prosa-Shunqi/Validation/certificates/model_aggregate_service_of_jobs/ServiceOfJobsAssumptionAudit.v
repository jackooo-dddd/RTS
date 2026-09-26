From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations ServiceOfJobsCorrespondence.

Goal Logic.True. idtac "AUDIT_BEGIN service_of_jobs_at_correspondence". exact Logic.I. Qed.
Print Assumptions service_of_jobs_at_correspondence.
Goal Logic.True. idtac "AUDIT_END service_of_jobs_at_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_of_jobs_correspondence". exact Logic.I. Qed.
Print Assumptions service_of_jobs_correspondence.
Goal Logic.True. idtac "AUDIT_END service_of_jobs_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_of_higher_or_equal_priority_jobs_correspondence". exact Logic.I. Qed.
Print Assumptions service_of_higher_or_equal_priority_jobs_correspondence.
Goal Logic.True. idtac "AUDIT_END service_of_higher_or_equal_priority_jobs_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_of_other_hep_jobs_correspondence". exact Logic.I. Qed.
Print Assumptions service_of_other_hep_jobs_correspondence.
Goal Logic.True. idtac "AUDIT_END service_of_other_hep_jobs_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_of_other_task_hep_jobs_correspondence". exact Logic.I. Qed.
Print Assumptions service_of_other_task_hep_jobs_correspondence.
Goal Logic.True. idtac "AUDIT_END service_of_other_task_hep_jobs_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_of_hep_jobs_correspondence". exact Logic.I. Qed.
Print Assumptions service_of_hep_jobs_correspondence.
Goal Logic.True. idtac "AUDIT_END service_of_hep_jobs_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN task_service_of_jobs_in_correspondence". exact Logic.I. Qed.
Print Assumptions task_service_of_jobs_in_correspondence.
Goal Logic.True. idtac "AUDIT_END task_service_of_jobs_in_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN total_service_of_jobs_in_correspondence". exact Logic.I. Qed.
Print Assumptions total_service_of_jobs_in_correspondence.
Goal Logic.True. idtac "AUDIT_END total_service_of_jobs_in_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN soj_sum_filter_related". exact Logic.I. Qed.
Print Assumptions soj_sum_filter_related.
Goal Logic.True. idtac "AUDIT_END soj_sum_filter_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN soj_ne_observation". exact Logic.I. Qed.
Print Assumptions soj_ne_observation.
Goal Logic.True. idtac "AUDIT_END soj_ne_observation". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN soj_ne_observation_transport". exact Logic.I. Qed.
Print Assumptions soj_ne_observation_transport.
Goal Logic.True. idtac "AUDIT_END soj_ne_observation_transport". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN soj_another_hep_job_related". exact Logic.I. Qed.
Print Assumptions soj_another_hep_job_related.
Goal Logic.True. idtac "AUDIT_END soj_another_hep_job_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN soj_another_task_hep_job_related". exact Logic.I. Qed.
Print Assumptions soj_another_task_hep_job_related.
Goal Logic.True. idtac "AUDIT_END soj_another_task_hep_job_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN soj_service_at_related". exact Logic.I. Qed.
Print Assumptions soj_service_at_related.
Goal Logic.True. idtac "AUDIT_END soj_service_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN soj_service_during_related". exact Logic.I. Qed.
Print Assumptions soj_service_during_related.
Goal Logic.True. idtac "AUDIT_END soj_service_during_related". exact Logic.I. Qed.
