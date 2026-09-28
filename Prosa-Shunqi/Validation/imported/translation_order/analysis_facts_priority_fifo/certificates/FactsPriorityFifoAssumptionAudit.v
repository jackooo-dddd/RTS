From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence PreemptionTimeCorrespondence PriorityDrivenCorrespondence PStateCoverHelpers FactsPreemptionHelpers WorkloadCorrespondence PriorityInversionCorrespondence ExistenceHelpers HepAtPtHelpers TaskPreemptionParametersCorrespondence BusyIntervalPiHelpers ServiceInversionPredCorrespondence BsiHelpers PcoBaseAdapter PcoStaticOrder PcoDynamicOrder PriorityCoercionCorrespondence FifoHelpers FactsPriorityFifoCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN hep_job_arrival_FIFO_correspondence". exact Logic.I. Qed.
Print Assumptions hep_job_arrival_FIFO_correspondence.
Goal Logic.True. idtac "AUDIT_END hep_job_arrival_FIFO_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN not_hep_job_arrival_FIFO_correspondence". exact Logic.I. Qed.
Print Assumptions not_hep_job_arrival_FIFO_correspondence.
Goal Logic.True. idtac "AUDIT_END not_hep_job_arrival_FIFO_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN not_hep_job_FIFO_correspondence". exact Logic.I. Qed.
Print Assumptions not_hep_job_FIFO_correspondence.
Goal Logic.True. idtac "AUDIT_END not_hep_job_FIFO_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN not_hep_job_always_higher_priority_FIFO_correspondence". exact Logic.I. Qed.
Print Assumptions not_hep_job_always_higher_priority_FIFO_correspondence.
Goal Logic.True. idtac "AUDIT_END not_hep_job_always_higher_priority_FIFO_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN FIFO_implies_no_priority_inversion_correspondence". exact Logic.I. Qed.
Print Assumptions FIFO_implies_no_priority_inversion_correspondence.
Goal Logic.True. idtac "AUDIT_END FIFO_implies_no_priority_inversion_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN scheduled_implies_higher_priority_completed_correspondence". exact Logic.I. Qed.
Print Assumptions scheduled_implies_higher_priority_completed_correspondence.
Goal Logic.True. idtac "AUDIT_END scheduled_implies_higher_priority_completed_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN FIFO_implies_no_pi_correspondence". exact Logic.I. Qed.
Print Assumptions FIFO_implies_no_pi_correspondence.
Goal Logic.True. idtac "AUDIT_END FIFO_implies_no_pi_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN FIFO_implies_no_service_inversion_correspondence". exact Logic.I. Qed.
Print Assumptions FIFO_implies_no_service_inversion_correspondence.
Goal Logic.True. idtac "AUDIT_END FIFO_implies_no_service_inversion_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN tasks_execute_sequentially_correspondence". exact Logic.I. Qed.
Print Assumptions tasks_execute_sequentially_correspondence.
Goal Logic.True. idtac "AUDIT_END tasks_execute_sequentially_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fifo_respects_sequential_tasks_correspondence". exact Logic.I. Qed.
Print Assumptions fifo_respects_sequential_tasks_correspondence.
Goal Logic.True. idtac "AUDIT_END fifo_respects_sequential_tasks_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN no_preemptions_under_FIFO_correspondence". exact Logic.I. Qed.
Print Assumptions no_preemptions_under_FIFO_correspondence.
Goal Logic.True. idtac "AUDIT_END no_preemptions_under_FIFO_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN FIFO_is_nonpreemptive_correspondence". exact Logic.I. Qed.
Print Assumptions FIFO_is_nonpreemptive_correspondence.
Goal Logic.True. idtac "AUDIT_END FIFO_is_nonpreemptive_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ffifo_eqP". exact Logic.I. Qed.
Print Assumptions ffifo_eqP.
Goal Logic.True. idtac "AUDIT_END ffifo_eqP". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ffifo_decidable_unique". exact Logic.I. Qed.
Print Assumptions ffifo_decidable_unique.
Goal Logic.True. idtac "AUDIT_END ffifo_decidable_unique". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ffifo_decidable_eq". exact Logic.I. Qed.
Print Assumptions ffifo_decidable_eq.
Goal Logic.True. idtac "AUDIT_END ffifo_decidable_eq". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ffifo_forall_task". exact Logic.I. Qed.
Print Assumptions ffifo_forall_task.
Goal Logic.True. idtac "AUDIT_END ffifo_forall_task". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ffifo_hep_related". exact Logic.I. Qed.
Print Assumptions ffifo_hep_related.
Goal Logic.True. idtac "AUDIT_END ffifo_hep_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ffifo_always_higher_priority_rel". exact Logic.I. Qed.
Print Assumptions ffifo_always_higher_priority_rel.
Goal Logic.True. idtac "AUDIT_END ffifo_always_higher_priority_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ffifo_basic_ready_rel". exact Logic.I. Qed.
Print Assumptions ffifo_basic_ready_rel.
Goal Logic.True. idtac "AUDIT_END ffifo_basic_ready_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ffifo_preempted_at_related". exact Logic.I. Qed.
Print Assumptions ffifo_preempted_at_related.
Goal Logic.True. idtac "AUDIT_END ffifo_preempted_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ffifo_no_superfluous_rel". exact Logic.I. Qed.
Print Assumptions ffifo_no_superfluous_rel.
Goal Logic.True. idtac "AUDIT_END ffifo_no_superfluous_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ffifo_nonpreemptive_rel". exact Logic.I. Qed.
Print Assumptions ffifo_nonpreemptive_rel.
Goal Logic.True. idtac "AUDIT_END ffifo_nonpreemptive_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ffifo_sequential_tasks_rel". exact Logic.I. Qed.
Print Assumptions ffifo_sequential_tasks_rel.
Goal Logic.True. idtac "AUDIT_END ffifo_sequential_tasks_rel". exact Logic.I. Qed.
