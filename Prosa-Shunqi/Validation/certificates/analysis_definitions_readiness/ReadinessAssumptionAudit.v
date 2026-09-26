From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations SequentialityCorrespondence ReadinessCorrespondence.

Goal Logic.True. idtac "AUDIT_BEGIN nonclairvoyant_readiness_correspondence". exact Logic.I. Qed.
Print Assumptions nonclairvoyant_readiness_correspondence.
Goal Logic.True. idtac "AUDIT_END nonclairvoyant_readiness_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN valid_nonpreemptive_readiness_correspondence". exact Logic.I. Qed.
Print Assumptions valid_nonpreemptive_readiness_correspondence.
Goal Logic.True. idtac "AUDIT_END valid_nonpreemptive_readiness_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sequential_readiness_correspondence". exact Logic.I. Qed.
Print Assumptions sequential_readiness_correspondence.
Goal Logic.True. idtac "AUDIT_END sequential_readiness_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rd_forall_cover_sprop". exact Logic.I. Qed.
Print Assumptions rd_forall_cover_sprop.
Goal Logic.True. idtac "AUDIT_END rd_forall_cover_sprop". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rd_lean_transport". exact Logic.I. Qed.
Print Assumptions rd_lean_transport.
Goal Logic.True. idtac "AUDIT_END rd_lean_transport". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rd_nat_input". exact Logic.I. Qed.
Print Assumptions rd_nat_input.
Goal Logic.True. idtac "AUDIT_END rd_nat_input". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rd_bool_eq_correspondence". exact Logic.I. Qed.
Print Assumptions rd_bool_eq_correspondence.
Goal Logic.True. idtac "AUDIT_END rd_bool_eq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rd_schedule_fun_to_svc". exact Logic.I. Qed.
Print Assumptions rd_schedule_fun_to_svc.
Goal Logic.True. idtac "AUDIT_END rd_schedule_fun_to_svc". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rd_schedule_to_target_rel". exact Logic.I. Qed.
Print Assumptions rd_schedule_to_target_rel.
Goal Logic.True. idtac "AUDIT_END rd_schedule_to_target_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rd_schedule_to_source_rel". exact Logic.I. Qed.
Print Assumptions rd_schedule_to_source_rel.
Goal Logic.True. idtac "AUDIT_END rd_schedule_to_source_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rd_state_eq_correspondence". exact Logic.I. Qed.
Print Assumptions rd_state_eq_correspondence.
Goal Logic.True. idtac "AUDIT_END rd_state_eq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rd_identical_prefix_correspondence". exact Logic.I. Qed.
Print Assumptions rd_identical_prefix_correspondence.
Goal Logic.True. idtac "AUDIT_END rd_identical_prefix_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rd_service_at_related". exact Logic.I. Qed.
Print Assumptions rd_service_at_related.
Goal Logic.True. idtac "AUDIT_END rd_service_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rd_service_related". exact Logic.I. Qed.
Print Assumptions rd_service_related.
Goal Logic.True. idtac "AUDIT_END rd_service_related". exact Logic.I. Qed.
