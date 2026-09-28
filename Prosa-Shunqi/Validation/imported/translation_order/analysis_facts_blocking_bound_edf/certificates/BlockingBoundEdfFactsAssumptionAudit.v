From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence PreemptionTimeCorrespondence PriorityDrivenCorrespondence PStateCoverHelpers FactsPreemptionHelpers WorkloadCorrespondence PriorityInversionCorrespondence ExistenceHelpers HepAtPtHelpers TaskPreemptionParametersCorrespondence BusyIntervalPiHelpers CurvesCorrespondence BlockingBoundEdfCorrespondence BlockingBoundEdfFactsCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN nonpreemptive_segments_bounded_by_blocking_correspondence". exact Logic.I. Qed.
Print Assumptions nonpreemptive_segments_bounded_by_blocking_correspondence.
Goal Logic.True. idtac "AUDIT_END nonpreemptive_segments_bounded_by_blocking_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbe_forall_list". exact Logic.I. Qed.
Print Assumptions bbe_forall_list.
Goal Logic.True. idtac "AUDIT_END bbe_forall_list". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbe_task_deadline_of_job_related". exact Logic.I. Qed.
Print Assumptions bbe_task_deadline_of_job_related.
Goal Logic.True. idtac "AUDIT_END bbe_task_deadline_of_job_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbe_deadline_related". exact Logic.I. Qed.
Print Assumptions bbe_deadline_related.
Goal Logic.True. idtac "AUDIT_END bbe_deadline_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbe_edf_rel". exact Logic.I. Qed.
Print Assumptions bbe_edf_rel.
Goal Logic.True. idtac "AUDIT_END bbe_edf_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbe_task_cost_of_job_related". exact Logic.I. Qed.
Print Assumptions bbe_task_cost_of_job_related.
Goal Logic.True. idtac "AUDIT_END bbe_task_cost_of_job_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbe_valid_job_costs_rel". exact Logic.I. Qed.
Print Assumptions bbe_valid_job_costs_rel.
Goal Logic.True. idtac "AUDIT_END bbe_valid_job_costs_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bbe_taskset_respects_rel". exact Logic.I. Qed.
Print Assumptions bbe_taskset_respects_rel.
Goal Logic.True. idtac "AUDIT_END bbe_taskset_respects_rel". exact Logic.I. Qed.
