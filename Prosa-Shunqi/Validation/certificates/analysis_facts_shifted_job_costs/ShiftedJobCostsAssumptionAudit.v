From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence TaskOffsetCorrespondence PeriodicCorrespondence NatSubCorrespondence LcmseqBaseAdapter LcmseqDivModAdapter LcmseqCorrespondence HyperperiodCorrespondence InfiniteJobsCorrespondence ShiftedJobCostsCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN job_costs_shifted_correspondence". exact Logic.I. Qed.
Print Assumptions job_costs_shifted_correspondence.
Goal Logic.True. idtac "AUDIT_END job_costs_shifted_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_costs_in_oi_correspondence". exact Logic.I. Qed.
Print Assumptions job_costs_in_oi_correspondence.
Goal Logic.True. idtac "AUDIT_END job_costs_in_oi_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_costs_shifted_valid_correspondence". exact Logic.I. Qed.
Print Assumptions job_costs_shifted_valid_correspondence.
Goal Logic.True. idtac "AUDIT_END job_costs_shifted_valid_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sjc_forall_list_correspondence". exact Logic.I. Qed.
Print Assumptions sjc_forall_list_correspondence.
Goal Logic.True. idtac "AUDIT_END sjc_forall_list_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sjc_cond_related". exact Logic.I. Qed.
Print Assumptions sjc_cond_related.
Goal Logic.True. idtac "AUDIT_END sjc_cond_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sjc_valid_job_costs_rel". exact Logic.I. Qed.
Print Assumptions sjc_valid_job_costs_rel.
Goal Logic.True. idtac "AUDIT_END sjc_valid_job_costs_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sjc_all_jobs_from_taskset_rel". exact Logic.I. Qed.
Print Assumptions sjc_all_jobs_from_taskset_rel.
Goal Logic.True. idtac "AUDIT_END sjc_all_jobs_from_taskset_rel". exact Logic.I. Qed.
