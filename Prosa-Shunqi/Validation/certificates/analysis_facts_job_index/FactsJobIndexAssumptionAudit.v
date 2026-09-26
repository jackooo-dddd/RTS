From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence FactsJobIndexCorrespondence.

Goal Logic.True. idtac "AUDIT_BEGIN case_arrival_lte_implies_equal_job_correspondence". exact Logic.I. Qed.
Print Assumptions case_arrival_lte_implies_equal_job_correspondence.
Goal Logic.True. idtac "AUDIT_END case_arrival_lte_implies_equal_job_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN case_arrival_gt_implies_equal_job_correspondence". exact Logic.I. Qed.
Print Assumptions case_arrival_gt_implies_equal_job_correspondence.
Goal Logic.True. idtac "AUDIT_END case_arrival_gt_implies_equal_job_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN equal_index_implies_equal_jobs_correspondence". exact Logic.I. Qed.
Print Assumptions equal_index_implies_equal_jobs_correspondence.
Goal Logic.True. idtac "AUDIT_END equal_index_implies_equal_jobs_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN diff_jobs_iff_diff_indices_correspondence". exact Logic.I. Qed.
Print Assumptions diff_jobs_iff_diff_indices_correspondence.
Goal Logic.True. idtac "AUDIT_END diff_jobs_iff_diff_indices_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN index_as_sum_size_and_index_correspondence". exact Logic.I. Qed.
Print Assumptions index_as_sum_size_and_index_correspondence.
Goal Logic.True. idtac "AUDIT_END index_as_sum_size_and_index_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arrival_lt_implies_job_in_arrivals_between_P_correspondence". exact Logic.I. Qed.
Print Assumptions arrival_lt_implies_job_in_arrivals_between_P_correspondence.
Goal Logic.True. idtac "AUDIT_END arrival_lt_implies_job_in_arrivals_between_P_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN index_lte_implies_arrival_lte_P_correspondence". exact Logic.I. Qed.
Print Assumptions index_lte_implies_arrival_lte_P_correspondence.
Goal Logic.True. idtac "AUDIT_END index_lte_implies_arrival_lte_P_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_index_same_in_task_arrivals_correspondence". exact Logic.I. Qed.
Print Assumptions job_index_same_in_task_arrivals_correspondence.
Goal Logic.True. idtac "AUDIT_END job_index_same_in_task_arrivals_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN index_job_lt_size_task_arrivals_up_to_job_correspondence". exact Logic.I. Qed.
Print Assumptions index_job_lt_size_task_arrivals_up_to_job_correspondence.
Goal Logic.True. idtac "AUDIT_END index_job_lt_size_task_arrivals_up_to_job_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN index_lte_implies_arrival_lte_correspondence". exact Logic.I. Qed.
Print Assumptions index_lte_implies_arrival_lte_correspondence.
Goal Logic.True. idtac "AUDIT_END index_lte_implies_arrival_lte_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN earlier_arrival_implies_lower_index_correspondence". exact Logic.I. Qed.
Print Assumptions earlier_arrival_implies_lower_index_correspondence.
Goal Logic.True. idtac "AUDIT_END earlier_arrival_implies_lower_index_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_index_minus_one_lt_size_task_arrivals_up_to_correspondence". exact Logic.I. Qed.
Print Assumptions job_index_minus_one_lt_size_task_arrivals_up_to_correspondence.
Goal Logic.True. idtac "AUDIT_END job_index_minus_one_lt_size_task_arrivals_up_to_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN positive_job_index_implies_positive_size_of_task_arrivals_correspondence". exact Logic.I. Qed.
Print Assumptions positive_job_index_implies_positive_size_of_task_arrivals_correspondence.
Goal Logic.True. idtac "AUDIT_END positive_job_index_implies_positive_size_of_task_arrivals_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN prev_job_arr_correspondence". exact Logic.I. Qed.
Print Assumptions prev_job_arr_correspondence.
Goal Logic.True. idtac "AUDIT_END prev_job_arr_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN prev_job_index_correspondence". exact Logic.I. Qed.
Print Assumptions prev_job_index_correspondence.
Goal Logic.True. idtac "AUDIT_END prev_job_index_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN prev_job_task_correspondence". exact Logic.I. Qed.
Print Assumptions prev_job_task_correspondence.
Goal Logic.True. idtac "AUDIT_END prev_job_task_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN prev_job_in_task_arrivals_up_to_j_correspondence". exact Logic.I. Qed.
Print Assumptions prev_job_in_task_arrivals_up_to_j_correspondence.
Goal Logic.True. idtac "AUDIT_END prev_job_in_task_arrivals_up_to_j_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN prev_job_arr_lte_correspondence". exact Logic.I. Qed.
Print Assumptions prev_job_arr_lte_correspondence.
Goal Logic.True. idtac "AUDIT_END prev_job_arr_lte_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN prev_job_index_j_correspondence". exact Logic.I. Qed.
Print Assumptions prev_job_index_j_correspondence.
Goal Logic.True. idtac "AUDIT_END prev_job_index_j_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN no_jobs_between_consecutive_jobs_correspondence". exact Logic.I. Qed.
Print Assumptions no_jobs_between_consecutive_jobs_correspondence.
Goal Logic.True. idtac "AUDIT_END no_jobs_between_consecutive_jobs_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN exists_jobs_before_j_correspondence". exact Logic.I. Qed.
Print Assumptions exists_jobs_before_j_correspondence.
Goal Logic.True. idtac "AUDIT_END exists_jobs_before_j_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fji_forall_pred". exact Logic.I. Qed.
Print Assumptions fji_forall_pred.
Goal Logic.True. idtac "AUDIT_END fji_forall_pred". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fji_not_correspondence". exact Logic.I. Qed.
Print Assumptions fji_not_correspondence.
Goal Logic.True. idtac "AUDIT_END fji_not_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fji_task_eq". exact Logic.I. Qed.
Print Assumptions fji_task_eq.
Goal Logic.True. idtac "AUDIT_END fji_task_eq". exact Logic.I. Qed.
