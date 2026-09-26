From FoundationCertificates Require Import
  PcoBaseAdapter PcoStaticOrder PcoDynamicOrder PriorityCoercionCorrespondence
  AnalysisPriorityClassesCorrespondence.

Goal Logic.True. idtac "AUDIT_BEGIN JLFP_FP_compatible_correspondence". exact Logic.I. Qed.
Print Assumptions JLFP_FP_compatible_correspondence.
Goal Logic.True. idtac "AUDIT_END JLFP_FP_compatible_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN apc_hp_task_related". exact Logic.I. Qed.
Print Assumptions apc_hp_task_related.
Goal Logic.True. idtac "AUDIT_END apc_hp_task_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN apc_hep_task_related". exact Logic.I. Qed.
Print Assumptions apc_hep_task_related.
Goal Logic.True. idtac "AUDIT_END apc_hep_task_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN apc_and_correspondence". exact Logic.I. Qed.
Print Assumptions apc_and_correspondence.
Goal Logic.True. idtac "AUDIT_END apc_and_correspondence". exact Logic.I. Qed.
