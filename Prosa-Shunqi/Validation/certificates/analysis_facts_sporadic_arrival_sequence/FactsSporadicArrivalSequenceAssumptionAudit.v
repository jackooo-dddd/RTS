From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence FactsSporadicArrivalSequenceCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN size_task_arrivals_at_leq_one_correspondence". exact Logic.I. Qed.
Print Assumptions size_task_arrivals_at_leq_one_correspondence.
Goal Logic.True. idtac "AUDIT_END size_task_arrivals_at_leq_one_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN only_j_in_task_arrivals_at_j_correspondence". exact Logic.I. Qed.
Print Assumptions only_j_in_task_arrivals_at_j_correspondence.
Goal Logic.True. idtac "AUDIT_END only_j_in_task_arrivals_at_j_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN only_j_at_job_arrival_j_correspondence". exact Logic.I. Qed.
Print Assumptions only_j_at_job_arrival_j_correspondence.
Goal Logic.True. idtac "AUDIT_END only_j_at_job_arrival_j_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN index_j_in_task_arrivals_at_correspondence". exact Logic.I. Qed.
Print Assumptions index_j_in_task_arrivals_at_correspondence.
Goal Logic.True. idtac "AUDIT_END index_j_in_task_arrivals_at_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN prev_job_arr_lt_correspondence". exact Logic.I. Qed.
Print Assumptions prev_job_arr_lt_correspondence.
Goal Logic.True. idtac "AUDIT_END prev_job_arr_lt_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN task_arrivals_at_as_task_arrivals_between_correspondence". exact Logic.I. Qed.
Print Assumptions task_arrivals_at_as_task_arrivals_between_correspondence.
Goal Logic.True. idtac "AUDIT_END task_arrivals_at_as_task_arrivals_between_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN prev_job_cat_correspondence". exact Logic.I. Qed.
Print Assumptions prev_job_cat_correspondence.
Goal Logic.True. idtac "AUDIT_END prev_job_cat_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsas_eq_correspondence". exact Logic.I. Qed.
Print Assumptions fsas_eq_correspondence.
Goal Logic.True. idtac "AUDIT_END fsas_eq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsas_false_correspondence". exact Logic.I. Qed.
Print Assumptions fsas_false_correspondence.
Goal Logic.True. idtac "AUDIT_END fsas_false_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsas_neq_correspondence". exact Logic.I. Qed.
Print Assumptions fsas_neq_correspondence.
Goal Logic.True. idtac "AUDIT_END fsas_neq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsas_exists_identity". exact Logic.I. Qed.
Print Assumptions fsas_exists_identity.
Goal Logic.True. idtac "AUDIT_END fsas_exists_identity". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsas_singleton_related". exact Logic.I. Qed.
Print Assumptions fsas_singleton_related.
Goal Logic.True. idtac "AUDIT_END fsas_singleton_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsas_valid_min_inter_arrival_related". exact Logic.I. Qed.
Print Assumptions fsas_valid_min_inter_arrival_related.
Goal Logic.True. idtac "AUDIT_END fsas_valid_min_inter_arrival_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsas_respects_sporadic_related". exact Logic.I. Qed.
Print Assumptions fsas_respects_sporadic_related.
Goal Logic.True. idtac "AUDIT_END fsas_respects_sporadic_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsas_prev_arrival_related". exact Logic.I. Qed.
Print Assumptions fsas_prev_arrival_related.
Goal Logic.True. idtac "AUDIT_END fsas_prev_arrival_related". exact Logic.I. Qed.
