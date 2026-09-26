From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations TardinessCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN task_tardiness_is_bounded_correspondence". exact Logic.I. Qed.
Print Assumptions task_tardiness_is_bounded_correspondence.
Goal Logic.True. idtac "AUDIT_END task_tardiness_is_bounded_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN trd_lean_transport". exact Logic.I. Qed.
Print Assumptions trd_lean_transport.
Goal Logic.True. idtac "AUDIT_END trd_lean_transport". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN trd_logic_eq_to_lean_eq". exact Logic.I. Qed.
Print Assumptions trd_logic_eq_to_lean_eq.
Goal Logic.True. idtac "AUDIT_END trd_logic_eq_to_lean_eq". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN trd_decide_eq_related". exact Logic.I. Qed.
Print Assumptions trd_decide_eq_related.
Goal Logic.True. idtac "AUDIT_END trd_decide_eq_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN trd_service_at_related". exact Logic.I. Qed.
Print Assumptions trd_service_at_related.
Goal Logic.True. idtac "AUDIT_END trd_service_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN trd_service_related". exact Logic.I. Qed.
Print Assumptions trd_service_related.
Goal Logic.True. idtac "AUDIT_END trd_service_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN trd_completed_by_related". exact Logic.I. Qed.
Print Assumptions trd_completed_by_related.
Goal Logic.True. idtac "AUDIT_END trd_completed_by_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN trd_job_of_task_related". exact Logic.I. Qed.
Print Assumptions trd_job_of_task_related.
Goal Logic.True. idtac "AUDIT_END trd_job_of_task_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN trd_task_response_time_bound_related". exact Logic.I. Qed.
Print Assumptions trd_task_response_time_bound_related.
Goal Logic.True. idtac "AUDIT_END trd_task_response_time_bound_related". exact Logic.I. Qed.
