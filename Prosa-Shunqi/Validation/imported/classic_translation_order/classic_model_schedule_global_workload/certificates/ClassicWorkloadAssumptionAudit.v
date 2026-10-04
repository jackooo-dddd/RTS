From FoundationCertificates Require Import ClassicWorkloadCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN Workload_service_of_task_correspondence". exact Logic.I. Qed.
Print Assumptions Workload_service_of_task_correspondence.
Goal Logic.True. idtac "AUDIT_END Workload_service_of_task_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Workload_workload_correspondence". exact Logic.I. Qed.
Print Assumptions Workload_workload_correspondence.
Goal Logic.True. idtac "AUDIT_END Workload_workload_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Workload_workload_joblist_correspondence". exact Logic.I. Qed.
Print Assumptions Workload_workload_joblist_correspondence.
Goal Logic.True. idtac "AUDIT_END Workload_workload_joblist_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Workload_workload_eq_workload_joblist_correspondence". exact Logic.I. Qed.
Print Assumptions Workload_workload_eq_workload_joblist_correspondence.
Goal Logic.True. idtac "AUDIT_END Workload_workload_eq_workload_joblist_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cs_forall_ncpus_sched". exact Logic.I. Qed.
Print Assumptions cs_forall_ncpus_sched.
Goal Logic.True. idtac "AUDIT_END cs_forall_ncpus_sched". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cs_ico". exact Logic.I. Qed.
Print Assumptions cs_ico.
Goal Logic.True. idtac "AUDIT_END cs_ico". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cs_undup_rel". exact Logic.I. Qed.
Print Assumptions cs_undup_rel.
Goal Logic.True. idtac "AUDIT_END cs_undup_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cs_bigcat_nat_rel". exact Logic.I. Qed.
Print Assumptions cs_bigcat_nat_rel.
Goal Logic.True. idtac "AUDIT_END cs_bigcat_nat_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cw_sumSeq". exact Logic.I. Qed.
Print Assumptions cw_sumSeq.
Goal Logic.True. idtac "AUDIT_END cw_sumSeq". exact Logic.I. Qed.
