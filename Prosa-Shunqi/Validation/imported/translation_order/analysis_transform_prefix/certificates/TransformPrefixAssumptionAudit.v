From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence TransformPrefixCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN prefix_map_correspondence". exact Logic.I. Qed.
Print Assumptions prefix_map_correspondence.
Goal Logic.True. idtac "AUDIT_END prefix_map_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN prefix_map_property_invariance_correspondence". exact Logic.I. Qed.
Print Assumptions prefix_map_property_invariance_correspondence.
Goal Logic.True. idtac "AUDIT_END prefix_map_property_invariance_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN prefix_map_pointwise_property_correspondence". exact Logic.I. Qed.
Print Assumptions prefix_map_pointwise_property_correspondence.
Goal Logic.True. idtac "AUDIT_END prefix_map_pointwise_property_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pfx_forall_cover_sprop". exact Logic.I. Qed.
Print Assumptions pfx_forall_cover_sprop.
Goal Logic.True. idtac "AUDIT_END pfx_forall_cover_sprop". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pfx_lean_transport". exact Logic.I. Qed.
Print Assumptions pfx_lean_transport.
Goal Logic.True. idtac "AUDIT_END pfx_lean_transport". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pfx_nat_input". exact Logic.I. Qed.
Print Assumptions pfx_nat_input.
Goal Logic.True. idtac "AUDIT_END pfx_nat_input". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pfx_schedule_to_target_rel". exact Logic.I. Qed.
Print Assumptions pfx_schedule_to_target_rel.
Goal Logic.True. idtac "AUDIT_END pfx_schedule_to_target_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pfx_schedule_to_source_rel". exact Logic.I. Qed.
Print Assumptions pfx_schedule_to_source_rel.
Goal Logic.True. idtac "AUDIT_END pfx_schedule_to_source_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pfx_prefix_map_canonical". exact Logic.I. Qed.
Print Assumptions pfx_prefix_map_canonical.
Goal Logic.True. idtac "AUDIT_END pfx_prefix_map_canonical". exact Logic.I. Qed.
