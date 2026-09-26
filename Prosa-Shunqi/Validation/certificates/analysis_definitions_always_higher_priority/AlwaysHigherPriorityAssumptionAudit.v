From FoundationCertificates Require Import
  PcoBaseAdapter PcoStaticOrder PcoDynamicOrder PriorityCoercionCorrespondence
  AlwaysHigherPriorityCorrespondence.

Goal Logic.True. idtac "AUDIT_BEGIN always_higher_priority_correspondence". exact Logic.I. Qed.
Print Assumptions always_higher_priority_correspondence.
Goal Logic.True. idtac "AUDIT_END always_higher_priority_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN always_higher_priority_jlfp_correspondence". exact Logic.I. Qed.
Print Assumptions always_higher_priority_jlfp_correspondence.
Goal Logic.True. idtac "AUDIT_END always_higher_priority_jlfp_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ahp_iff_correspondence". exact Logic.I. Qed.
Print Assumptions ahp_iff_correspondence.
Goal Logic.True. idtac "AUDIT_END ahp_iff_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN JLFP_to_JLDP_correspondence". exact Logic.I. Qed.
Print Assumptions JLFP_to_JLDP_correspondence.
Goal Logic.True. idtac "AUDIT_END JLFP_to_JLDP_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pco_forall_jlfp". exact Logic.I. Qed.
Print Assumptions pco_forall_jlfp.
Goal Logic.True. idtac "AUDIT_END pco_forall_jlfp". exact Logic.I. Qed.
