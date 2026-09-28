From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence PreemptionTimeCorrespondence PriorityDrivenCorrespondence PStateCoverHelpers FactsPreemptionHelpers WorkloadCorrespondence PriorityInversionCorrespondence ExistenceHelpers HepAtPtHelpers TaskPreemptionParametersCorrespondence BusyIntervalPiHelpers CurvesCorrespondence NatSubCorrespondence PcoBaseAdapter PcoStaticOrder PcoDynamicOrder PriorityCoercionCorrespondence PriorityGelHelpers PriorityElfHelpers BlockingBoundElfCorrespondence FactsBlockingBoundElfCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN nonpreemptive_segments_bounded_by_blocking_correspondence". exact Logic.I. Qed.
Print Assumptions nonpreemptive_segments_bounded_by_blocking_correspondence.
Goal Logic.True. idtac "AUDIT_END nonpreemptive_segments_bounded_by_blocking_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fbbelf_forall_list". exact Logic.I. Qed.
Print Assumptions fbbelf_forall_list.
Goal Logic.True. idtac "AUDIT_END fbbelf_forall_list". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fbbelf_elf_rel". exact Logic.I. Qed.
Print Assumptions fbbelf_elf_rel.
Goal Logic.True. idtac "AUDIT_END fbbelf_elf_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fbbelf_task_cost_of_job_related". exact Logic.I. Qed.
Print Assumptions fbbelf_task_cost_of_job_related.
Goal Logic.True. idtac "AUDIT_END fbbelf_task_cost_of_job_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fbbelf_valid_job_costs_rel". exact Logic.I. Qed.
Print Assumptions fbbelf_valid_job_costs_rel.
Goal Logic.True. idtac "AUDIT_END fbbelf_valid_job_costs_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fbbelf_taskset_respects_rel". exact Logic.I. Qed.
Print Assumptions fbbelf_taskset_respects_rel.
Goal Logic.True. idtac "AUDIT_END fbbelf_taskset_respects_rel". exact Logic.I. Qed.
