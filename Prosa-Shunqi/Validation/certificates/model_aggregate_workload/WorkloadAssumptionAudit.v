From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  WorkloadCorrespondence.

Goal Logic.True. idtac "AUDIT_BEGIN workload_of_jobs_correspondence". exact Logic.I. Qed.
Print Assumptions workload_of_jobs_correspondence.
Goal Logic.True. idtac "AUDIT_END workload_of_jobs_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN task_workload_correspondence". exact Logic.I. Qed.
Print Assumptions task_workload_correspondence.
Goal Logic.True. idtac "AUDIT_END task_workload_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN task_workload_between_correspondence". exact Logic.I. Qed.
Print Assumptions task_workload_between_correspondence.
Goal Logic.True. idtac "AUDIT_END task_workload_between_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN workload_of_job_correspondence". exact Logic.I. Qed.
Print Assumptions workload_of_job_correspondence.
Goal Logic.True. idtac "AUDIT_END workload_of_job_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN total_workload_correspondence". exact Logic.I. Qed.
Print Assumptions total_workload_correspondence.
Goal Logic.True. idtac "AUDIT_END total_workload_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN total_workload_between_correspondence". exact Logic.I. Qed.
Print Assumptions total_workload_between_correspondence.
Goal Logic.True. idtac "AUDIT_END total_workload_between_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN workload_of_hep_jobs_correspondence". exact Logic.I. Qed.
Print Assumptions workload_of_hep_jobs_correspondence.
Goal Logic.True. idtac "AUDIT_END workload_of_hep_jobs_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN workload_of_other_hep_jobs_correspondence". exact Logic.I. Qed.
Print Assumptions workload_of_other_hep_jobs_correspondence.
Goal Logic.True. idtac "AUDIT_END workload_of_other_hep_jobs_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wl_sum_filter_related". exact Logic.I. Qed.
Print Assumptions wl_sum_filter_related.
Goal Logic.True. idtac "AUDIT_END wl_sum_filter_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wl_ne_observation". exact Logic.I. Qed.
Print Assumptions wl_ne_observation.
Goal Logic.True. idtac "AUDIT_END wl_ne_observation". exact Logic.I. Qed.
