From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations InterferenceCorrespondence.

Goal Logic.True. idtac "AUDIT_BEGIN hp_task_interference_correspondence". exact Logic.I. Qed.
Print Assumptions hp_task_interference_correspondence.
Goal Logic.True. idtac "AUDIT_END hp_task_interference_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ep_task_hep_job_correspondence". exact Logic.I. Qed.
Print Assumptions ep_task_hep_job_correspondence.
Goal Logic.True. idtac "AUDIT_END ep_task_hep_job_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN other_ep_task_hep_job_correspondence". exact Logic.I. Qed.
Print Assumptions other_ep_task_hep_job_correspondence.
Goal Logic.True. idtac "AUDIT_END other_ep_task_hep_job_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN hep_job_from_other_ep_task_interference_correspondence". exact Logic.I. Qed.
Print Assumptions hep_job_from_other_ep_task_interference_correspondence.
Goal Logic.True. idtac "AUDIT_END hep_job_from_other_ep_task_interference_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN hp_task_hep_job_correspondence". exact Logic.I. Qed.
Print Assumptions hp_task_hep_job_correspondence.
Goal Logic.True. idtac "AUDIT_END hp_task_hep_job_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN hep_job_from_hp_task_interference_correspondence". exact Logic.I. Qed.
Print Assumptions hep_job_from_hp_task_interference_correspondence.
Goal Logic.True. idtac "AUDIT_END hep_job_from_hp_task_interference_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cumulative_interference_from_hep_jobs_from_hp_tasks_correspondence". exact Logic.I. Qed.
Print Assumptions cumulative_interference_from_hep_jobs_from_hp_tasks_correspondence.
Goal Logic.True. idtac "AUDIT_END cumulative_interference_from_hep_jobs_from_hp_tasks_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cumulative_interference_from_hep_jobs_from_other_ep_tasks_correspondence". exact Logic.I. Qed.
Print Assumptions cumulative_interference_from_hep_jobs_from_other_ep_tasks_correspondence.
Goal Logic.True. idtac "AUDIT_END cumulative_interference_from_hep_jobs_from_other_ep_tasks_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN another_hep_job_interference_correspondence". exact Logic.I. Qed.
Print Assumptions another_hep_job_interference_correspondence.
Goal Logic.True. idtac "AUDIT_END another_hep_job_interference_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN another_task_hep_job_interference_correspondence". exact Logic.I. Qed.
Print Assumptions another_task_hep_job_interference_correspondence.
Goal Logic.True. idtac "AUDIT_END another_task_hep_job_interference_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN another_hep_job_of_same_task_interference_correspondence". exact Logic.I. Qed.
Print Assumptions another_hep_job_of_same_task_interference_correspondence.
Goal Logic.True. idtac "AUDIT_END another_hep_job_of_same_task_interference_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN other_hep_jobs_interfering_workload_correspondence". exact Logic.I. Qed.
Print Assumptions other_hep_jobs_interfering_workload_correspondence.
Goal Logic.True. idtac "AUDIT_END other_hep_jobs_interfering_workload_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cumulative_another_hep_job_interference_correspondence". exact Logic.I. Qed.
Print Assumptions cumulative_another_hep_job_interference_correspondence.
Goal Logic.True. idtac "AUDIT_END cumulative_another_hep_job_interference_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cumulative_another_task_hep_job_interference_correspondence". exact Logic.I. Qed.
Print Assumptions cumulative_another_task_hep_job_interference_correspondence.
Goal Logic.True. idtac "AUDIT_END cumulative_another_task_hep_job_interference_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cumulative_other_hep_jobs_interfering_workload_correspondence". exact Logic.I. Qed.
Print Assumptions cumulative_other_hep_jobs_interfering_workload_correspondence.
Goal Logic.True. idtac "AUDIT_END cumulative_other_hep_jobs_interfering_workload_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN if_bool_or_related". exact Logic.I. Qed.
Print Assumptions if_bool_or_related.
Goal Logic.True. idtac "AUDIT_END if_bool_or_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN if_has_canonical". exact Logic.I. Qed.
Print Assumptions if_has_canonical.
Goal Logic.True. idtac "AUDIT_END if_has_canonical". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN if_lean_transport". exact Logic.I. Qed.
Print Assumptions if_lean_transport.
Goal Logic.True. idtac "AUDIT_END if_lean_transport". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN if_has_related". exact Logic.I. Qed.
Print Assumptions if_has_related.
Goal Logic.True. idtac "AUDIT_END if_has_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN if_ne_observation". exact Logic.I. Qed.
Print Assumptions if_ne_observation.
Goal Logic.True. idtac "AUDIT_END if_ne_observation". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN if_ne_transport". exact Logic.I. Qed.
Print Assumptions if_ne_transport.
Goal Logic.True. idtac "AUDIT_END if_ne_transport". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN if_eq_transport". exact Logic.I. Qed.
Print Assumptions if_eq_transport.
Goal Logic.True. idtac "AUDIT_END if_eq_transport". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN if_bool_to_nat_related". exact Logic.I. Qed.
Print Assumptions if_bool_to_nat_related.
Goal Logic.True. idtac "AUDIT_END if_bool_to_nat_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN if_sum_filter_related". exact Logic.I. Qed.
Print Assumptions if_sum_filter_related.
Goal Logic.True. idtac "AUDIT_END if_sum_filter_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN if_hp_task_canonical". exact Logic.I. Qed.
Print Assumptions if_hp_task_canonical.
Goal Logic.True. idtac "AUDIT_END if_hp_task_canonical". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN if_ep_task_canonical". exact Logic.I. Qed.
Print Assumptions if_ep_task_canonical.
Goal Logic.True. idtac "AUDIT_END if_ep_task_canonical". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN if_hp_task_jobs". exact Logic.I. Qed.
Print Assumptions if_hp_task_jobs.
Goal Logic.True. idtac "AUDIT_END if_hp_task_jobs". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN if_ep_task_jobs". exact Logic.I. Qed.
Print Assumptions if_ep_task_jobs.
Goal Logic.True. idtac "AUDIT_END if_ep_task_jobs". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN if_another_hep_job_related". exact Logic.I. Qed.
Print Assumptions if_another_hep_job_related.
Goal Logic.True. idtac "AUDIT_END if_another_hep_job_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN if_another_task_hep_job_related". exact Logic.I. Qed.
Print Assumptions if_another_task_hep_job_related.
Goal Logic.True. idtac "AUDIT_END if_another_task_hep_job_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN if_another_hep_job_of_same_task_related". exact Logic.I. Qed.
Print Assumptions if_another_hep_job_of_same_task_related.
Goal Logic.True. idtac "AUDIT_END if_another_hep_job_of_same_task_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN if_service_at_related". exact Logic.I. Qed.
Print Assumptions if_service_at_related.
Goal Logic.True. idtac "AUDIT_END if_service_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN if_receives_service_at_related". exact Logic.I. Qed.
Print Assumptions if_receives_service_at_related.
Goal Logic.True. idtac "AUDIT_END if_receives_service_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN if_served_jobs_at_related". exact Logic.I. Qed.
Print Assumptions if_served_jobs_at_related.
Goal Logic.True. idtac "AUDIT_END if_served_jobs_at_related". exact Logic.I. Qed.
