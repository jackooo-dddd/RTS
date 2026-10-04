From FoundationCertificates Require Import ClassicTasksetMembershipCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN TaskSetMembership_actual_response_time_correspondence". exact Logic.I. Qed.
Print Assumptions TaskSetMembership_actual_response_time_correspondence.
Goal Logic.True. idtac "AUDIT_END TaskSetMembership_actual_response_time_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN TaskSetMembership_actual_response_time_is_valid_correspondence". exact Logic.I. Qed.
Print Assumptions TaskSetMembership_actual_response_time_is_valid_correspondence.
Goal Logic.True. idtac "AUDIT_END TaskSetMembership_actual_response_time_is_valid_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN TaskSetMembership_actual_response_time_is_minimum_correspondence". exact Logic.I. Qed.
Print Assumptions TaskSetMembership_actual_response_time_is_minimum_correspondence.
Goal Logic.True. idtac "AUDIT_END TaskSetMembership_actual_response_time_is_minimum_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN TaskSetMembership_ts_membership_inflated_job_cost_positive_correspondence". exact Logic.I. Qed.
Print Assumptions TaskSetMembership_ts_membership_inflated_job_cost_positive_correspondence.
Goal Logic.True. idtac "AUDIT_END TaskSetMembership_ts_membership_inflated_job_cost_positive_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN TaskSetMembership_ts_membership_inflated_job_cost_le_inflated_task_cost_correspondence". exact Logic.I. Qed.
Print Assumptions TaskSetMembership_ts_membership_inflated_job_cost_le_inflated_task_cost_correspondence.
Goal Logic.True. idtac "AUDIT_END TaskSetMembership_ts_membership_inflated_job_cost_le_inflated_task_cost_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN TaskSetMembership_response_time_bound_in_sched_susp_highercost_correspondence". exact Logic.I. Qed.
Print Assumptions TaskSetMembership_response_time_bound_in_sched_susp_highercost_correspondence.
Goal Logic.True. idtac "AUDIT_END TaskSetMembership_response_time_bound_in_sched_susp_highercost_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN TaskSetMembership_ts_membership_difference_in_response_times_correspondence". exact Logic.I. Qed.
Print Assumptions TaskSetMembership_ts_membership_difference_in_response_times_correspondence.
Goal Logic.True. idtac "AUDIT_END TaskSetMembership_ts_membership_difference_in_response_times_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN TaskSetMembership_ts_membership_job_jitter_le_task_jitter_correspondence". exact Logic.I. Qed.
Print Assumptions TaskSetMembership_ts_membership_job_jitter_le_task_jitter_correspondence.
Goal Logic.True. idtac "AUDIT_END TaskSetMembership_ts_membership_job_jitter_le_task_jitter_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ctm_forall_sched". exact Logic.I. Qed.
Print Assumptions ctm_forall_sched.
Goal Logic.True. idtac "AUDIT_END ctm_forall_sched". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ctm_forall_par". exact Logic.I. Qed.
Print Assumptions ctm_forall_par.
Goal Logic.True. idtac "AUDIT_END ctm_forall_par". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ctm_forall_arr". exact Logic.I. Qed.
Print Assumptions ctm_forall_arr.
Goal Logic.True. idtac "AUDIT_END ctm_forall_arr". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ctm_forall_rel". exact Logic.I. Qed.
Print Assumptions ctm_forall_rel.
Goal Logic.True. idtac "AUDIT_END ctm_forall_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ctm_forall_susp". exact Logic.I. Qed.
Print Assumptions ctm_forall_susp.
Goal Logic.True. idtac "AUDIT_END ctm_forall_susp". exact Logic.I. Qed.
