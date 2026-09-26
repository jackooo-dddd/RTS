From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence WorkloadCorrespondence WorkloadBoundedCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN athep_workload_is_bounded_correspondence". exact Logic.I. Qed.
Print Assumptions athep_workload_is_bounded_correspondence.
Goal Logic.True. idtac "AUDIT_END athep_workload_is_bounded_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wlb_logic_eq_to_lean_eq". exact Logic.I. Qed.
Print Assumptions wlb_logic_eq_to_lean_eq.
Goal Logic.True. idtac "AUDIT_END wlb_logic_eq_to_lean_eq". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wlb_lean_transport". exact Logic.I. Qed.
Print Assumptions wlb_lean_transport.
Goal Logic.True. idtac "AUDIT_END wlb_lean_transport". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wlb_decide_eq_related". exact Logic.I. Qed.
Print Assumptions wlb_decide_eq_related.
Goal Logic.True. idtac "AUDIT_END wlb_decide_eq_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wlb_quiet_time_related". exact Logic.I. Qed.
Print Assumptions wlb_quiet_time_related.
Goal Logic.True. idtac "AUDIT_END wlb_quiet_time_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wlb_job_of_task_related". exact Logic.I. Qed.
Print Assumptions wlb_job_of_task_related.
Goal Logic.True. idtac "AUDIT_END wlb_job_of_task_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wlb_another_task_hep_job_related". exact Logic.I. Qed.
Print Assumptions wlb_another_task_hep_job_related.
Goal Logic.True. idtac "AUDIT_END wlb_another_task_hep_job_related". exact Logic.I. Qed.
