From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence PeriodicCorrespondence TmiaCorrespondence FactsPeriodicMaxInterArrivalCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN max_inter_eq_period_correspondence". exact Logic.I. Qed.
Print Assumptions max_inter_eq_period_correspondence.
Goal Logic.True. idtac "AUDIT_END max_inter_eq_period_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN valid_period_is_valid_max_inter_arrival_time_correspondence". exact Logic.I. Qed.
Print Assumptions valid_period_is_valid_max_inter_arrival_time_correspondence.
Goal Logic.True. idtac "AUDIT_END valid_period_is_valid_max_inter_arrival_time_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN periodic_model_respects_max_inter_arrival_model_correspondence". exact Logic.I. Qed.
Print Assumptions periodic_model_respects_max_inter_arrival_model_correspondence.
Goal Logic.True. idtac "AUDIT_END periodic_model_respects_max_inter_arrival_model_correspondence". exact Logic.I. Qed.
