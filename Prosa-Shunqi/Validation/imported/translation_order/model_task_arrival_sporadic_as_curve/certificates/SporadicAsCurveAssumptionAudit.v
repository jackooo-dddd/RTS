From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence NatSubCorrespondence DivModCorrespondence CurvesCorrespondence SporadicAsCurveCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN MaxArrivalsSporadic_correspondence". exact Logic.I. Qed.
Print Assumptions MaxArrivalsSporadic_correspondence.
Goal Logic.True. idtac "AUDIT_END MaxArrivalsSporadic_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sporadic_arrival_curve_valid_correspondence". exact Logic.I. Qed.
Print Assumptions sporadic_arrival_curve_valid_correspondence.
Goal Logic.True. idtac "AUDIT_END sporadic_arrival_curve_valid_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sporadic_task_sets_arrival_curve_valid_correspondence". exact Logic.I. Qed.
Print Assumptions sporadic_task_sets_arrival_curve_valid_correspondence.
Goal Logic.True. idtac "AUDIT_END sporadic_task_sets_arrival_curve_valid_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sporadic_arrival_curve_respects_max_arrivals_correspondence". exact Logic.I. Qed.
Print Assumptions sporadic_arrival_curve_respects_max_arrivals_correspondence.
Goal Logic.True. idtac "AUDIT_END sporadic_arrival_curve_respects_max_arrivals_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sporadic_task_sets_respects_max_arrivals_correspondence". exact Logic.I. Qed.
Print Assumptions sporadic_task_sets_respects_max_arrivals_correspondence.
Goal Logic.True. idtac "AUDIT_END sporadic_task_sets_respects_max_arrivals_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sac_forall_list". exact Logic.I. Qed.
Print Assumptions sac_forall_list.
Goal Logic.True. idtac "AUDIT_END sac_forall_list". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sac_eq_correspondence". exact Logic.I. Qed.
Print Assumptions sac_eq_correspondence.
Goal Logic.True. idtac "AUDIT_END sac_eq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sac_false_correspondence". exact Logic.I. Qed.
Print Assumptions sac_false_correspondence.
Goal Logic.True. idtac "AUDIT_END sac_false_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sac_neq_correspondence". exact Logic.I. Qed.
Print Assumptions sac_neq_correspondence.
Goal Logic.True. idtac "AUDIT_END sac_neq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sac_max_sporadic_arrivals_related". exact Logic.I. Qed.
Print Assumptions sac_max_sporadic_arrivals_related.
Goal Logic.True. idtac "AUDIT_END sac_max_sporadic_arrivals_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sac_valid_min_inter_arrival_related". exact Logic.I. Qed.
Print Assumptions sac_valid_min_inter_arrival_related.
Goal Logic.True. idtac "AUDIT_END sac_valid_min_inter_arrival_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sac_respects_sporadic_related". exact Logic.I. Qed.
Print Assumptions sac_respects_sporadic_related.
Goal Logic.True. idtac "AUDIT_END sac_respects_sporadic_related". exact Logic.I. Qed.
