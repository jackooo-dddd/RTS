From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence WorkloadCorrespondence JlfpWithFpCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN other_ep_task_correspondence". exact Logic.I. Qed.
Print Assumptions other_ep_task_correspondence.
Goal Logic.True. idtac "AUDIT_END other_ep_task_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN hep_job_of_ep_other_task_correspondence". exact Logic.I. Qed.
Print Assumptions hep_job_of_ep_other_task_correspondence.
Goal Logic.True. idtac "AUDIT_END hep_job_of_ep_other_task_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN hep_workload_from_other_ep_partitioned_by_tasks_correspondence". exact Logic.I. Qed.
Print Assumptions hep_workload_from_other_ep_partitioned_by_tasks_correspondence.
Goal Logic.True. idtac "AUDIT_END hep_workload_from_other_ep_partitioned_by_tasks_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN from_hp_task_correspondence". exact Logic.I. Qed.
Print Assumptions from_hp_task_correspondence.
Goal Logic.True. idtac "AUDIT_END from_hp_task_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN hep_from_hp_task_correspondence". exact Logic.I. Qed.
Print Assumptions hep_from_hp_task_correspondence.
Goal Logic.True. idtac "AUDIT_END hep_from_hp_task_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN hep_from_ep_task_correspondence". exact Logic.I. Qed.
Print Assumptions hep_from_ep_task_correspondence.
Goal Logic.True. idtac "AUDIT_END hep_from_ep_task_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN hep_hp_workload_hp_correspondence". exact Logic.I. Qed.
Print Assumptions hep_hp_workload_hp_correspondence.
Goal Logic.True. idtac "AUDIT_END hep_hp_workload_hp_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN hep_workload_partitioning_taskwise_correspondence". exact Logic.I. Qed.
Print Assumptions hep_workload_partitioning_taskwise_correspondence.
Goal Logic.True. idtac "AUDIT_END hep_workload_partitioning_taskwise_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jwf_forall_list". exact Logic.I. Qed.
Print Assumptions jwf_forall_list.
Goal Logic.True. idtac "AUDIT_END jwf_forall_list". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jwf_arrival_sequence_to_source_rel". exact Logic.I. Qed.
Print Assumptions jwf_arrival_sequence_to_source_rel.
Goal Logic.True. idtac "AUDIT_END jwf_arrival_sequence_to_source_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jwf_forall_arrival_sequence". exact Logic.I. Qed.
Print Assumptions jwf_forall_arrival_sequence.
Goal Logic.True. idtac "AUDIT_END jwf_forall_arrival_sequence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jwf_ne_transport". exact Logic.I. Qed.
Print Assumptions jwf_ne_transport.
Goal Logic.True. idtac "AUDIT_END jwf_ne_transport". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jwf_eq_transport". exact Logic.I. Qed.
Print Assumptions jwf_eq_transport.
Goal Logic.True. idtac "AUDIT_END jwf_eq_transport". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jwf_bool_not_related". exact Logic.I. Qed.
Print Assumptions jwf_bool_not_related.
Goal Logic.True. idtac "AUDIT_END jwf_bool_not_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jwf_ep_task_related". exact Logic.I. Qed.
Print Assumptions jwf_ep_task_related.
Goal Logic.True. idtac "AUDIT_END jwf_ep_task_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jwf_hp_task_related". exact Logic.I. Qed.
Print Assumptions jwf_hp_task_related.
Goal Logic.True. idtac "AUDIT_END jwf_hp_task_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jwf_compatible_related". exact Logic.I. Qed.
Print Assumptions jwf_compatible_related.
Goal Logic.True. idtac "AUDIT_END jwf_compatible_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jwf_all_jobs_from_taskset_related". exact Logic.I. Qed.
Print Assumptions jwf_all_jobs_from_taskset_related.
Goal Logic.True. idtac "AUDIT_END jwf_all_jobs_from_taskset_related". exact Logic.I. Qed.
