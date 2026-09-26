From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations FactsTaskArrivalsCorrespondence.

Goal Logic.True. idtac "AUDIT_BEGIN num_arrivals_of_task_cat_correspondence". exact Logic.I. Qed.
Print Assumptions num_arrivals_of_task_cat_correspondence.
Goal Logic.True. idtac "AUDIT_END num_arrivals_of_task_cat_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN task_arrivals_between_cat_correspondence". exact Logic.I. Qed.
Print Assumptions task_arrivals_between_cat_correspondence.
Goal Logic.True. idtac "AUDIT_END task_arrivals_between_cat_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN task_arrivals_up_to_prefix_cat_correspondence". exact Logic.I. Qed.
Print Assumptions task_arrivals_up_to_prefix_cat_correspondence.
Goal Logic.True. idtac "AUDIT_END task_arrivals_up_to_prefix_cat_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arrives_in_task_arrivals_up_to_correspondence". exact Logic.I. Qed.
Print Assumptions arrives_in_task_arrivals_up_to_correspondence.
Goal Logic.True. idtac "AUDIT_END arrives_in_task_arrivals_up_to_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arrives_in_task_arrivals_at_correspondence". exact Logic.I. Qed.
Print Assumptions arrives_in_task_arrivals_at_correspondence.
Goal Logic.True. idtac "AUDIT_END arrives_in_task_arrivals_at_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN task_arrivals_cat_correspondence". exact Logic.I. Qed.
Print Assumptions task_arrivals_cat_correspondence.
Goal Logic.True. idtac "AUDIT_END task_arrivals_cat_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN task_arrivals_up_to_cat_correspondence". exact Logic.I. Qed.
Print Assumptions task_arrivals_up_to_cat_correspondence.
Goal Logic.True. idtac "AUDIT_END task_arrivals_up_to_cat_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_in_task_arrivals_between_correspondence". exact Logic.I. Qed.
Print Assumptions job_in_task_arrivals_between_correspondence.
Goal Logic.True. idtac "AUDIT_END job_in_task_arrivals_between_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN task_arrivals_between_subset_correspondence". exact Logic.I. Qed.
Print Assumptions task_arrivals_between_subset_correspondence.
Goal Logic.True. idtac "AUDIT_END task_arrivals_between_subset_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arrives_in_task_arrivals_implies_arrived_correspondence". exact Logic.I. Qed.
Print Assumptions arrives_in_task_arrivals_implies_arrived_correspondence.
Goal Logic.True. idtac "AUDIT_END arrives_in_task_arrivals_implies_arrived_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arrives_in_task_arrivals_before_implies_arrives_before_correspondence". exact Logic.I. Qed.
Print Assumptions arrives_in_task_arrivals_before_implies_arrives_before_correspondence.
Goal Logic.True. idtac "AUDIT_END arrives_in_task_arrivals_before_implies_arrives_before_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arrives_in_task_arrivals_implies_job_task_correspondence". exact Logic.I. Qed.
Print Assumptions arrives_in_task_arrivals_implies_job_task_correspondence.
Goal Logic.True. idtac "AUDIT_END arrives_in_task_arrivals_implies_job_task_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN in_task_arrivals_between_implies_job_of_task_correspondence". exact Logic.I. Qed.
Print Assumptions in_task_arrivals_between_implies_job_of_task_correspondence.
Goal Logic.True. idtac "AUDIT_END in_task_arrivals_between_implies_job_of_task_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN task_arrivals_nonempty_correspondence". exact Logic.I. Qed.
Print Assumptions task_arrivals_nonempty_correspondence.
Goal Logic.True. idtac "AUDIT_END task_arrivals_nonempty_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN number_of_task_arrivals_nonzero_correspondence". exact Logic.I. Qed.
Print Assumptions number_of_task_arrivals_nonzero_correspondence.
Goal Logic.True. idtac "AUDIT_END number_of_task_arrivals_nonzero_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN uniq_task_arrivals_correspondence". exact Logic.I. Qed.
Print Assumptions uniq_task_arrivals_correspondence.
Goal Logic.True. idtac "AUDIT_END uniq_task_arrivals_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN task_arrivals_between_uniq_correspondence". exact Logic.I. Qed.
Print Assumptions task_arrivals_between_uniq_correspondence.
Goal Logic.True. idtac "AUDIT_END task_arrivals_between_uniq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_notin_task_arrivals_before_correspondence". exact Logic.I. Qed.
Print Assumptions job_notin_task_arrivals_before_correspondence.
Goal Logic.True. idtac "AUDIT_END job_notin_task_arrivals_before_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arrival_lt_implies_strict_prefix_correspondence". exact Logic.I. Qed.
Print Assumptions arrival_lt_implies_strict_prefix_correspondence.
Goal Logic.True. idtac "AUDIT_END arrival_lt_implies_strict_prefix_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN nth_job_of_task_arrivals_correspondence". exact Logic.I. Qed.
Print Assumptions nth_job_of_task_arrivals_correspondence.
Goal Logic.True. idtac "AUDIT_END nth_job_of_task_arrivals_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN task_arrivals_between_is_cat_of_task_arrivals_at_correspondence". exact Logic.I. Qed.
Print Assumptions task_arrivals_between_is_cat_of_task_arrivals_at_correspondence.
Goal Logic.True. idtac "AUDIT_END task_arrivals_between_is_cat_of_task_arrivals_at_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN size_of_task_arrivals_between_correspondence". exact Logic.I. Qed.
Print Assumptions size_of_task_arrivals_between_correspondence.
Goal Logic.True. idtac "AUDIT_END size_of_task_arrivals_between_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN task_arrivals_between_sorted_correspondence". exact Logic.I. Qed.
Print Assumptions task_arrivals_between_sorted_correspondence.
Goal Logic.True. idtac "AUDIT_END task_arrivals_between_sorted_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ta_prefix_of_related". exact Logic.I. Qed.
Print Assumptions ta_prefix_of_related.
Goal Logic.True. idtac "AUDIT_END ta_prefix_of_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ta_strict_prefix_of_related". exact Logic.I. Qed.
Print Assumptions ta_strict_prefix_of_related.
Goal Logic.True. idtac "AUDIT_END ta_strict_prefix_of_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ta_interval_sum_related". exact Logic.I. Qed.
Print Assumptions ta_interval_sum_related.
Goal Logic.True. idtac "AUDIT_END ta_interval_sum_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ta_list_sum_fold". exact Logic.I. Qed.
Print Assumptions ta_list_sum_fold.
Goal Logic.True. idtac "AUDIT_END ta_list_sum_fold". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ta_forall_arrival_sequence". exact Logic.I. Qed.
Print Assumptions ta_forall_arrival_sequence.
Goal Logic.True. idtac "AUDIT_END ta_forall_arrival_sequence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ta_sorted_ischain". exact Logic.I. Qed.
Print Assumptions ta_sorted_ischain.
Goal Logic.True. idtac "AUDIT_END ta_sorted_ischain". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ta_exists_list". exact Logic.I. Qed.
Print Assumptions ta_exists_list.
Goal Logic.True. idtac "AUDIT_END ta_exists_list". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ta_job_task_eq_decide". exact Logic.I. Qed.
Print Assumptions ta_job_task_eq_decide.
Goal Logic.True. idtac "AUDIT_END ta_job_task_eq_decide". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ta_by_arrival_times_related". exact Logic.I. Qed.
Print Assumptions ta_by_arrival_times_related.
Goal Logic.True. idtac "AUDIT_END ta_by_arrival_times_related". exact Logic.I. Qed.
