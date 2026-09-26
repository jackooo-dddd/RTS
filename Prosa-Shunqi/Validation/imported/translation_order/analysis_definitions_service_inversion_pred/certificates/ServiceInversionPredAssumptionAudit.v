From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence ServiceInversionPredCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN service_inversion_correspondence". exact Logic.I. Qed.
Print Assumptions service_inversion_correspondence.
Goal Logic.True. idtac "AUDIT_END service_inversion_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cumulative_service_inversion_correspondence". exact Logic.I. Qed.
Print Assumptions cumulative_service_inversion_correspondence.
Goal Logic.True. idtac "AUDIT_END cumulative_service_inversion_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pred_service_inversion_of_job_is_bounded_by_correspondence". exact Logic.I. Qed.
Print Assumptions pred_service_inversion_of_job_is_bounded_by_correspondence.
Goal Logic.True. idtac "AUDIT_END pred_service_inversion_of_job_is_bounded_by_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pred_service_inversion_is_bounded_by_correspondence". exact Logic.I. Qed.
Print Assumptions pred_service_inversion_is_bounded_by_correspondence.
Goal Logic.True. idtac "AUDIT_END pred_service_inversion_is_bounded_by_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sip_lean_transport". exact Logic.I. Qed.
Print Assumptions sip_lean_transport.
Goal Logic.True. idtac "AUDIT_END sip_lean_transport". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sip_logic_eq_to_lean_eq". exact Logic.I. Qed.
Print Assumptions sip_logic_eq_to_lean_eq.
Goal Logic.True. idtac "AUDIT_END sip_logic_eq_to_lean_eq". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sip_decide_eq_related". exact Logic.I. Qed.
Print Assumptions sip_decide_eq_related.
Goal Logic.True. idtac "AUDIT_END sip_decide_eq_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sip_bool_to_nat_related". exact Logic.I. Qed.
Print Assumptions sip_bool_to_nat_related.
Goal Logic.True. idtac "AUDIT_END sip_bool_to_nat_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sip_has_canonical". exact Logic.I. Qed.
Print Assumptions sip_has_canonical.
Goal Logic.True. idtac "AUDIT_END sip_has_canonical". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sip_has_related". exact Logic.I. Qed.
Print Assumptions sip_has_related.
Goal Logic.True. idtac "AUDIT_END sip_has_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sip_service_at_related". exact Logic.I. Qed.
Print Assumptions sip_service_at_related.
Goal Logic.True. idtac "AUDIT_END sip_service_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sip_receives_service_at_related". exact Logic.I. Qed.
Print Assumptions sip_receives_service_at_related.
Goal Logic.True. idtac "AUDIT_END sip_receives_service_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sip_served_jobs_at_related". exact Logic.I. Qed.
Print Assumptions sip_served_jobs_at_related.
Goal Logic.True. idtac "AUDIT_END sip_served_jobs_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sip_job_of_task_related". exact Logic.I. Qed.
Print Assumptions sip_job_of_task_related.
Goal Logic.True. idtac "AUDIT_END sip_job_of_task_related". exact Logic.I. Qed.
