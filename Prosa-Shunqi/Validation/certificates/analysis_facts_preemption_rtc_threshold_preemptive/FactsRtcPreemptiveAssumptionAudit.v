From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence TaskPreemptionParametersCorrespondence TaskPreemptionFullyPreemptiveCorrespondence FactsRtcPreemptiveCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN fully_preemptive_valid_task_run_to_completion_threshold_correspondence". exact Logic.I. Qed.
Print Assumptions fully_preemptive_valid_task_run_to_completion_threshold_correspondence.
Goal Logic.True. idtac "AUDIT_END fully_preemptive_valid_task_run_to_completion_threshold_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frp_lean_transport". exact Logic.I. Qed.
Print Assumptions frp_lean_transport.
Goal Logic.True. idtac "AUDIT_END frp_lean_transport". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frp_fully_preemptive_job_related". exact Logic.I. Qed.
Print Assumptions frp_fully_preemptive_job_related.
Goal Logic.True. idtac "AUDIT_END frp_fully_preemptive_job_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frp_task_cost_of_job_related". exact Logic.I. Qed.
Print Assumptions frp_task_cost_of_job_related.
Goal Logic.True. idtac "AUDIT_END frp_task_cost_of_job_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frp_valid_job_costs_related". exact Logic.I. Qed.
Print Assumptions frp_valid_job_costs_related.
Goal Logic.True. idtac "AUDIT_END frp_valid_job_costs_related". exact Logic.I. Qed.
