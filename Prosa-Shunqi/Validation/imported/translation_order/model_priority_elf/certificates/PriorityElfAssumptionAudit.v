From FoundationCertificates Require Import
  NatSubCorrespondence PcoBaseAdapter PcoStaticOrder PcoDynamicOrder PriorityCoercionCorrespondence PriorityGelCorrespondence PriorityElfCorrespondence.

Goal Logic.True. idtac "AUDIT_BEGIN ELF_correspondence". exact Logic.I. Qed.
Print Assumptions ELF_correspondence.
Goal Logic.True. idtac "AUDIT_END ELF_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN elf_hep_task_related". exact Logic.I. Qed.
Print Assumptions elf_hep_task_related.
Goal Logic.True. idtac "AUDIT_END elf_hep_task_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN elf_hp_task_related". exact Logic.I. Qed.
Print Assumptions elf_hp_task_related.
Goal Logic.True. idtac "AUDIT_END elf_hp_task_related". exact Logic.I. Qed.
