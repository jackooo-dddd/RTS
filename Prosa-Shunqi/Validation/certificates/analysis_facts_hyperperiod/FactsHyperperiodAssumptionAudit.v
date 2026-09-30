From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence TaskOffsetCorrespondence PeriodicCorrespondence NatSubCorrespondence LcmseqBaseAdapter LcmseqDivModAdapter LcmseqCorrespondence HyperperiodCorrespondence InfiniteJobsCorrespondence FactsHyperperiodCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN hyperperiod_int_mult_of_any_task_correspondence". exact Logic.I. Qed.
Print Assumptions hyperperiod_int_mult_of_any_task_correspondence.
Goal Logic.True. idtac "AUDIT_END hyperperiod_int_mult_of_any_task_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN valid_periods_imply_pos_hp_correspondence". exact Logic.I. Qed.
Print Assumptions valid_periods_imply_pos_hp_correspondence.
Goal Logic.True. idtac "AUDIT_END valid_periods_imply_pos_hp_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN corresponding_jobs_have_same_task_correspondence". exact Logic.I. Qed.
Print Assumptions corresponding_jobs_have_same_task_correspondence.
Goal Logic.True. idtac "AUDIT_END corresponding_jobs_have_same_task_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN all_jobs_arrive_within_hyperperiod_correspondence". exact Logic.I. Qed.
Print Assumptions all_jobs_arrive_within_hyperperiod_correspondence.
Goal Logic.True. idtac "AUDIT_END all_jobs_arrive_within_hyperperiod_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN eq_size_hyp_lt_correspondence". exact Logic.I. Qed.
Print Assumptions eq_size_hyp_lt_correspondence.
Goal Logic.True. idtac "AUDIT_END eq_size_hyp_lt_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN eq_size_of_arrivals_in_hyperperiod_correspondence". exact Logic.I. Qed.
Print Assumptions eq_size_of_arrivals_in_hyperperiod_correspondence.
Goal Logic.True. idtac "AUDIT_END eq_size_of_arrivals_in_hyperperiod_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_in_hp_arrives_in_task_arrivals_up_to_correspondence". exact Logic.I. Qed.
Print Assumptions job_in_hp_arrives_in_task_arrivals_up_to_correspondence.
Goal Logic.True. idtac "AUDIT_END job_in_hp_arrives_in_task_arrivals_up_to_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_in_own_hp_correspondence". exact Logic.I. Qed.
Print Assumptions job_in_own_hp_correspondence.
Goal Logic.True. idtac "AUDIT_END job_in_own_hp_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN corr_job_in_task_arrivals_up_to_correspondence". exact Logic.I. Qed.
Print Assumptions corr_job_in_task_arrivals_up_to_correspondence.
Goal Logic.True. idtac "AUDIT_END corr_job_in_task_arrivals_up_to_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN corresponding_job_arrives_correspondence". exact Logic.I. Qed.
Print Assumptions corresponding_job_arrives_correspondence.
Goal Logic.True. idtac "AUDIT_END corresponding_job_arrives_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fhyp_forall_list_correspondence". exact Logic.I. Qed.
Print Assumptions fhyp_forall_list_correspondence.
Goal Logic.True. idtac "AUDIT_END fhyp_forall_list_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fhyp_eq_identity_correspondence". exact Logic.I. Qed.
Print Assumptions fhyp_eq_identity_correspondence.
Goal Logic.True. idtac "AUDIT_END fhyp_eq_identity_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fhyp_corr_job_related". exact Logic.I. Qed.
Print Assumptions fhyp_corr_job_related.
Goal Logic.True. idtac "AUDIT_END fhyp_corr_job_related". exact Logic.I. Qed.
