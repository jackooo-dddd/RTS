From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  NatSubCorrespondence DivModCorrespondence FactsSporadicArrivalBoundCorrespondence.

Goal Logic.True. idtac "AUDIT_BEGIN max_sporadic_arrivals_correspondence". exact Logic.I. Qed.
Print Assumptions max_sporadic_arrivals_correspondence.
Goal Logic.True. idtac "AUDIT_END max_sporadic_arrivals_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arrival_of_nth_job_correspondence". exact Logic.I. Qed.
Print Assumptions arrival_of_nth_job_correspondence.
Goal Logic.True. idtac "AUDIT_END arrival_of_nth_job_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN minimum_distance_for_n_sporadic_arrivals_correspondence". exact Logic.I. Qed.
Print Assumptions minimum_distance_for_n_sporadic_arrivals_correspondence.
Goal Logic.True. idtac "AUDIT_END minimum_distance_for_n_sporadic_arrivals_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sporadic_task_arrivals_bound_correspondence". exact Logic.I. Qed.
Print Assumptions sporadic_task_arrivals_bound_correspondence.
Goal Logic.True. idtac "AUDIT_END sporadic_task_arrivals_bound_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsb_eq_correspondence". exact Logic.I. Qed.
Print Assumptions fsb_eq_correspondence.
Goal Logic.True. idtac "AUDIT_END fsb_eq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsb_false_correspondence". exact Logic.I. Qed.
Print Assumptions fsb_false_correspondence.
Goal Logic.True. idtac "AUDIT_END fsb_false_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsb_neq_correspondence". exact Logic.I. Qed.
Print Assumptions fsb_neq_correspondence.
Goal Logic.True. idtac "AUDIT_END fsb_neq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsb_valid_min_inter_arrival_related". exact Logic.I. Qed.
Print Assumptions fsb_valid_min_inter_arrival_related.
Goal Logic.True. idtac "AUDIT_END fsb_valid_min_inter_arrival_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsb_respects_sporadic_related". exact Logic.I. Qed.
Print Assumptions fsb_respects_sporadic_related.
Goal Logic.True. idtac "AUDIT_END fsb_respects_sporadic_related". exact Logic.I. Qed.
