From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence PreemptionTimeCorrespondence PriorityDrivenCorrespondence PStateCoverHelpers FactsPreemptionHelpers WorkloadCorrespondence PriorityInversionCorrespondence ExistenceHelpers HepAtPtHelpers TaskPreemptionParametersCorrespondence BusyIntervalPiCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN lower_priority_job_scheduled_implies_no_preemption_time_correspondence". exact Logic.I. Qed.
Print Assumptions lower_priority_job_scheduled_implies_no_preemption_time_correspondence.
Goal Logic.True. idtac "AUDIT_END lower_priority_job_scheduled_implies_no_preemption_time_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN lower_priority_job_continuously_scheduled_correspondence". exact Logic.I. Qed.
Print Assumptions lower_priority_job_continuously_scheduled_correspondence.
Goal Logic.True. idtac "AUDIT_END lower_priority_job_continuously_scheduled_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN low_priority_job_arrives_before_busy_interval_prefix_correspondence". exact Logic.I. Qed.
Print Assumptions low_priority_job_arrives_before_busy_interval_prefix_correspondence.
Goal Logic.True. idtac "AUDIT_END low_priority_job_arrives_before_busy_interval_prefix_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN low_priority_job_scheduled_before_busy_interval_prefix_correspondence". exact Logic.I. Qed.
Print Assumptions low_priority_job_scheduled_before_busy_interval_prefix_correspondence.
Goal Logic.True. idtac "AUDIT_END low_priority_job_scheduled_before_busy_interval_prefix_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN lp_job_should_arrive_early_for_pi_correspondence". exact Logic.I. Qed.
Print Assumptions lp_job_should_arrive_early_for_pi_correspondence.
Goal Logic.True. idtac "AUDIT_END lp_job_should_arrive_early_for_pi_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN lower_priority_jobs_never_scheduled_if_no_inversion_correspondence". exact Logic.I. Qed.
Print Assumptions lower_priority_jobs_never_scheduled_if_no_inversion_correspondence.
Goal Logic.True. idtac "AUDIT_END lower_priority_jobs_never_scheduled_if_no_inversion_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN no_preemption_time_before_pi_correspondence". exact Logic.I. Qed.
Print Assumptions no_preemption_time_before_pi_correspondence.
Goal Logic.True. idtac "AUDIT_END no_preemption_time_before_pi_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pi_job_remains_scheduled_correspondence". exact Logic.I. Qed.
Print Assumptions pi_job_remains_scheduled_correspondence.
Goal Logic.True. idtac "AUDIT_END pi_job_remains_scheduled_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pi_continuous_correspondence". exact Logic.I. Qed.
Print Assumptions pi_continuous_correspondence.
Goal Logic.True. idtac "AUDIT_END pi_continuous_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN only_one_pi_job_correspondence". exact Logic.I. Qed.
Print Assumptions only_one_pi_job_correspondence.
Goal Logic.True. idtac "AUDIT_END only_one_pi_job_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN busy_interval_pi_cases_correspondence". exact Logic.I. Qed.
Print Assumptions busy_interval_pi_cases_correspondence.
Goal Logic.True. idtac "AUDIT_END busy_interval_pi_cases_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN max_lp_nonpreemptive_segment_correspondence". exact Logic.I. Qed.
Print Assumptions max_lp_nonpreemptive_segment_correspondence.
Goal Logic.True. idtac "AUDIT_END max_lp_nonpreemptive_segment_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN max_np_job_segment_bounded_by_max_np_task_segment_correspondence". exact Logic.I. Qed.
Print Assumptions max_np_job_segment_bounded_by_max_np_task_segment_correspondence.
Goal Logic.True. idtac "AUDIT_END max_np_job_segment_bounded_by_max_np_task_segment_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN hp_job_not_scheduled_before_quiet_time_correspondence". exact Logic.I. Qed.
Print Assumptions hp_job_not_scheduled_before_quiet_time_correspondence.
Goal Logic.True. idtac "AUDIT_END hp_job_not_scheduled_before_quiet_time_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN preemption_time_exists_case1_correspondence". exact Logic.I. Qed.
Print Assumptions preemption_time_exists_case1_correspondence.
Goal Logic.True. idtac "AUDIT_END preemption_time_exists_case1_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN preemption_time_exists_case2_correspondence". exact Logic.I. Qed.
Print Assumptions preemption_time_exists_case2_correspondence.
Goal Logic.True. idtac "AUDIT_END preemption_time_exists_case2_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN no_intermediate_preemption_point_correspondence". exact Logic.I. Qed.
Print Assumptions no_intermediate_preemption_point_correspondence.
Goal Logic.True. idtac "AUDIT_END no_intermediate_preemption_point_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN continuously_scheduled_between_preemption_points_correspondence". exact Logic.I. Qed.
Print Assumptions continuously_scheduled_between_preemption_points_correspondence.
Goal Logic.True. idtac "AUDIT_END continuously_scheduled_between_preemption_points_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN first_preemption_time_correspondence". exact Logic.I. Qed.
Print Assumptions first_preemption_time_correspondence.
Goal Logic.True. idtac "AUDIT_END first_preemption_time_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN preemption_time_le_max_len_of_np_segment_correspondence". exact Logic.I. Qed.
Print Assumptions preemption_time_le_max_len_of_np_segment_correspondence.
Goal Logic.True. idtac "AUDIT_END preemption_time_le_max_len_of_np_segment_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN preemption_time_exists_case3_correspondence". exact Logic.I. Qed.
Print Assumptions preemption_time_exists_case3_correspondence.
Goal Logic.True. idtac "AUDIT_END preemption_time_exists_case3_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN preemption_time_exists_correspondence". exact Logic.I. Qed.
Print Assumptions preemption_time_exists_correspondence.
Goal Logic.True. idtac "AUDIT_END preemption_time_exists_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN no_priority_inversion_after_preemption_point_correspondence". exact Logic.I. Qed.
Print Assumptions no_priority_inversion_after_preemption_point_correspondence.
Goal Logic.True. idtac "AUDIT_END no_priority_inversion_after_preemption_point_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN priority_inversion_occurs_only_till_preemption_point_correspondence". exact Logic.I. Qed.
Print Assumptions priority_inversion_occurs_only_till_preemption_point_correspondence.
Goal Logic.True. idtac "AUDIT_END priority_inversion_occurs_only_till_preemption_point_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bpi_bigmax_canonical". exact Logic.I. Qed.
Print Assumptions bpi_bigmax_canonical.
Goal Logic.True. idtac "AUDIT_END bpi_bigmax_canonical". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bpi_bigmax_related". exact Logic.I. Qed.
Print Assumptions bpi_bigmax_related.
Goal Logic.True. idtac "AUDIT_END bpi_bigmax_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bpi_forall_tms". exact Logic.I. Qed.
Print Assumptions bpi_forall_tms.
Goal Logic.True. idtac "AUDIT_END bpi_forall_tms". exact Logic.I. Qed.
