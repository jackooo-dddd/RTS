From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence PeriodicCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN PeriodicModel_source_total". exact Logic.I. Qed.
Print Assumptions PeriodicModel_source_total.
Goal Logic.True. idtac "AUDIT_END PeriodicModel_source_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN PeriodicModel_target_total". exact Logic.I. Qed.
Print Assumptions PeriodicModel_target_total.
Goal Logic.True. idtac "AUDIT_END PeriodicModel_target_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN valid_period_correspondence". exact Logic.I. Qed.
Print Assumptions valid_period_correspondence.
Goal Logic.True. idtac "AUDIT_END valid_period_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN respects_periodic_task_model_correspondence". exact Logic.I. Qed.
Print Assumptions respects_periodic_task_model_correspondence.
Goal Logic.True. idtac "AUDIT_END respects_periodic_task_model_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN valid_periods_correspondence". exact Logic.I. Qed.
Print Assumptions valid_periods_correspondence.
Goal Logic.True. idtac "AUDIT_END valid_periods_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN taskset_respects_periodic_task_model_correspondence". exact Logic.I. Qed.
Print Assumptions taskset_respects_periodic_task_model_correspondence.
Goal Logic.True. idtac "AUDIT_END taskset_respects_periodic_task_model_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN per_eq_correspondence". exact Logic.I. Qed.
Print Assumptions per_eq_correspondence.
Goal Logic.True. idtac "AUDIT_END per_eq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN per_exists_identity". exact Logic.I. Qed.
Print Assumptions per_exists_identity.
Goal Logic.True. idtac "AUDIT_END per_exists_identity". exact Logic.I. Qed.
