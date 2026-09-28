From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence PreemptionTimeCorrespondence PriorityDrivenCorrespondence PStateCoverHelpers FactsPreemptionHelpers NatSubCorrespondence PcoBaseAdapter PcoStaticOrder PcoDynamicOrder PriorityCoercionCorrespondence PriorityGelHelpers PriorityElfHelpers FactsPriorityElfCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN hep_job_elf_gel_correspondence". exact Logic.I. Qed.
Print Assumptions hep_job_elf_gel_correspondence.
Goal Logic.True. idtac "AUDIT_END hep_job_elf_gel_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN hep_job_arrival_elf_correspondence". exact Logic.I. Qed.
Print Assumptions hep_job_arrival_elf_correspondence.
Goal Logic.True. idtac "AUDIT_END hep_job_arrival_elf_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ELF_is_reflexive_correspondence". exact Logic.I. Qed.
Print Assumptions ELF_is_reflexive_correspondence.
Goal Logic.True. idtac "AUDIT_END ELF_is_reflexive_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ELF_is_transitive_correspondence". exact Logic.I. Qed.
Print Assumptions ELF_is_transitive_correspondence.
Goal Logic.True. idtac "AUDIT_END ELF_is_transitive_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ELF_is_total_correspondence". exact Logic.I. Qed.
Print Assumptions ELF_is_total_correspondence.
Goal Logic.True. idtac "AUDIT_END ELF_is_total_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ELF_is_JLFP_FP_compatible_correspondence". exact Logic.I. Qed.
Print Assumptions ELF_is_JLFP_FP_compatible_correspondence.
Goal Logic.True. idtac "AUDIT_END ELF_is_JLFP_FP_compatible_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ELF_respects_sequential_tasks_correspondence". exact Logic.I. Qed.
Print Assumptions ELF_respects_sequential_tasks_correspondence.
Goal Logic.True. idtac "AUDIT_END ELF_respects_sequential_tasks_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ELF_implies_sequential_tasks_correspondence". exact Logic.I. Qed.
Print Assumptions ELF_implies_sequential_tasks_correspondence.
Goal Logic.True. idtac "AUDIT_END ELF_implies_sequential_tasks_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN felf_exists_identity". exact Logic.I. Qed.
Print Assumptions felf_exists_identity.
Goal Logic.True. idtac "AUDIT_END felf_exists_identity". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN felf_elf_rel". exact Logic.I. Qed.
Print Assumptions felf_elf_rel.
Goal Logic.True. idtac "AUDIT_END felf_elf_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN felf_gel_rel". exact Logic.I. Qed.
Print Assumptions felf_gel_rel.
Goal Logic.True. idtac "AUDIT_END felf_gel_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN felf_hep_task_related". exact Logic.I. Qed.
Print Assumptions felf_hep_task_related.
Goal Logic.True. idtac "AUDIT_END felf_hep_task_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN felf_hp_task_related". exact Logic.I. Qed.
Print Assumptions felf_hp_task_related.
Goal Logic.True. idtac "AUDIT_END felf_hp_task_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN felf_ep_task_related". exact Logic.I. Qed.
Print Assumptions felf_ep_task_related.
Goal Logic.True. idtac "AUDIT_END felf_ep_task_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN felf_same_task_related". exact Logic.I. Qed.
Print Assumptions felf_same_task_related.
Goal Logic.True. idtac "AUDIT_END felf_same_task_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN felf_sequential_tasks_rel". exact Logic.I. Qed.
Print Assumptions felf_sequential_tasks_rel.
Goal Logic.True. idtac "AUDIT_END felf_sequential_tasks_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN felf_work_bearing_rel". exact Logic.I. Qed.
Print Assumptions felf_work_bearing_rel.
Goal Logic.True. idtac "AUDIT_END felf_work_bearing_rel". exact Logic.I. Qed.
