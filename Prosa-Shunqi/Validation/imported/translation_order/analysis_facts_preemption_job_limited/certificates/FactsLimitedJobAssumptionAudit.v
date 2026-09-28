From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence LimitedPreemptiveCorrespondence ScheduleLimitedPreemptiveCorrespondence FactsLimitedJobCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN zero_in_preemption_points_correspondence". exact Logic.I. Qed.
Print Assumptions zero_in_preemption_points_correspondence.
Goal Logic.True. idtac "AUDIT_END zero_in_preemption_points_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN zero_is_first_element_correspondence". exact Logic.I. Qed.
Print Assumptions zero_is_first_element_correspondence.
Goal Logic.True. idtac "AUDIT_END zero_is_first_element_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN list_of_preemption_point_is_not_empty_correspondence". exact Logic.I. Qed.
Print Assumptions list_of_preemption_point_is_not_empty_correspondence.
Goal Logic.True. idtac "AUDIT_END list_of_preemption_point_is_not_empty_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_cost_in_nonpreemptive_points_correspondence". exact Logic.I. Qed.
Print Assumptions job_cost_in_nonpreemptive_points_correspondence.
Goal Logic.True. idtac "AUDIT_END job_cost_in_nonpreemptive_points_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN number_of_preemption_points_at_least_two_correspondence". exact Logic.I. Qed.
Print Assumptions number_of_preemption_points_at_least_two_correspondence.
Goal Logic.True. idtac "AUDIT_END number_of_preemption_points_at_least_two_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN antidensity_of_preemption_points_correspondence". exact Logic.I. Qed.
Print Assumptions antidensity_of_preemption_points_correspondence.
Goal Logic.True. idtac "AUDIT_END antidensity_of_preemption_points_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN work_belongs_to_some_nonpreemptive_segment_correspondence". exact Logic.I. Qed.
Print Assumptions work_belongs_to_some_nonpreemptive_segment_correspondence.
Goal Logic.True. idtac "AUDIT_END work_belongs_to_some_nonpreemptive_segment_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_parameters_last_np_to_job_limited_correspondence". exact Logic.I. Qed.
Print Assumptions job_parameters_last_np_to_job_limited_correspondence.
Goal Logic.True. idtac "AUDIT_END job_parameters_last_np_to_job_limited_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_parameters_max_np_to_job_limited_correspondence". exact Logic.I. Qed.
Print Assumptions job_parameters_max_np_to_job_limited_correspondence.
Goal Logic.True. idtac "AUDIT_END job_parameters_max_np_to_job_limited_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN valid_fixed_preemption_points_model_lemma_correspondence". exact Logic.I. Qed.
Print Assumptions valid_fixed_preemption_points_model_lemma_correspondence.
Goal Logic.True. idtac "AUDIT_END valid_fixed_preemption_points_model_lemma_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN flj_first0_canonical". exact Logic.I. Qed.
Print Assumptions flj_first0_canonical.
Goal Logic.True. idtac "AUDIT_END flj_first0_canonical". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN flj_first0_related". exact Logic.I. Qed.
Print Assumptions flj_first0_related.
Goal Logic.True. idtac "AUDIT_END flj_first0_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN flj_job_cost_positive_related". exact Logic.I. Qed.
Print Assumptions flj_job_cost_positive_related.
Goal Logic.True. idtac "AUDIT_END flj_job_cost_positive_related". exact Logic.I. Qed.
