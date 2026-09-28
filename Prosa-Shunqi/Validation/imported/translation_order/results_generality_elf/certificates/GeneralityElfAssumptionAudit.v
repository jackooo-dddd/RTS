From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence PreemptionTimeCorrespondence PriorityDrivenCorrespondence PStateCoverHelpers FactsPreemptionHelpers NatSubCorrespondence PcoBaseAdapter PcoStaticOrder PcoDynamicOrder PriorityCoercionCorrespondence PriorityGelHelpers PriorityElfHelpers GeneralityElfCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN elf_generalizes_gel_correspondence". exact Logic.I. Qed.
Print Assumptions elf_generalizes_gel_correspondence.
Goal Logic.True. idtac "AUDIT_END elf_generalizes_gel_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN elf_is_fixed_priority_correspondence". exact Logic.I. Qed.
Print Assumptions elf_is_fixed_priority_correspondence.
Goal Logic.True. idtac "AUDIT_END elf_is_fixed_priority_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN elf_generalizes_fixed_priority_correspondence". exact Logic.I. Qed.
Print Assumptions elf_generalizes_fixed_priority_correspondence.
Goal Logic.True. idtac "AUDIT_END elf_generalizes_fixed_priority_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN gelf_iff_correspondence". exact Logic.I. Qed.
Print Assumptions gelf_iff_correspondence.
Goal Logic.True. idtac "AUDIT_END gelf_iff_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN gelf_forall_sched". exact Logic.I. Qed.
Print Assumptions gelf_forall_sched.
Goal Logic.True. idtac "AUDIT_END gelf_forall_sched". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN gelf_elf_rel". exact Logic.I. Qed.
Print Assumptions gelf_elf_rel.
Goal Logic.True. idtac "AUDIT_END gelf_elf_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN gelf_gel_rel". exact Logic.I. Qed.
Print Assumptions gelf_gel_rel.
Goal Logic.True. idtac "AUDIT_END gelf_gel_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN gelf_ep_task_related". exact Logic.I. Qed.
Print Assumptions gelf_ep_task_related.
Goal Logic.True. idtac "AUDIT_END gelf_ep_task_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN gelf_same_task_related". exact Logic.I. Qed.
Print Assumptions gelf_same_task_related.
Goal Logic.True. idtac "AUDIT_END gelf_same_task_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN gelf_respects_elf_rel". exact Logic.I. Qed.
Print Assumptions gelf_respects_elf_rel.
Goal Logic.True. idtac "AUDIT_END gelf_respects_elf_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN gelf_respects_gel_rel". exact Logic.I. Qed.
Print Assumptions gelf_respects_gel_rel.
Goal Logic.True. idtac "AUDIT_END gelf_respects_gel_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN gelf_respects_fp_rel". exact Logic.I. Qed.
Print Assumptions gelf_respects_fp_rel.
Goal Logic.True. idtac "AUDIT_END gelf_respects_fp_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN gelf_valid_schedule_rel". exact Logic.I. Qed.
Print Assumptions gelf_valid_schedule_rel.
Goal Logic.True. idtac "AUDIT_END gelf_valid_schedule_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN gelf_sequential_tasks_rel". exact Logic.I. Qed.
Print Assumptions gelf_sequential_tasks_rel.
Goal Logic.True. idtac "AUDIT_END gelf_sequential_tasks_rel". exact Logic.I. Qed.
