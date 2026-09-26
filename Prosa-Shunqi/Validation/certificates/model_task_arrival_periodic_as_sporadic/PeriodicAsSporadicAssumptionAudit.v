From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence PeriodicCorrespondence PeriodicAsSporadicCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN periodic_as_sporadic_correspondence". exact Logic.I. Qed.
Print Assumptions periodic_as_sporadic_correspondence.
Goal Logic.True. idtac "AUDIT_END periodic_as_sporadic_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN valid_period_is_valid_inter_arrival_time_correspondence". exact Logic.I. Qed.
Print Assumptions valid_period_is_valid_inter_arrival_time_correspondence.
Goal Logic.True. idtac "AUDIT_END valid_period_is_valid_inter_arrival_time_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN periodic_task_respects_sporadic_task_model_correspondence". exact Logic.I. Qed.
Print Assumptions periodic_task_respects_sporadic_task_model_correspondence.
Goal Logic.True. idtac "AUDIT_END periodic_task_respects_sporadic_task_model_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN valid_periods_are_valid_inter_arrival_times_correspondence". exact Logic.I. Qed.
Print Assumptions valid_periods_are_valid_inter_arrival_times_correspondence.
Goal Logic.True. idtac "AUDIT_END valid_periods_are_valid_inter_arrival_times_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN periodic_task_sets_respect_sporadic_task_model_correspondence". exact Logic.I. Qed.
Print Assumptions periodic_task_sets_respect_sporadic_task_model_correspondence.
Goal Logic.True. idtac "AUDIT_END periodic_task_sets_respect_sporadic_task_model_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pas_forall_list". exact Logic.I. Qed.
Print Assumptions pas_forall_list.
Goal Logic.True. idtac "AUDIT_END pas_forall_list". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pas_false_correspondence". exact Logic.I. Qed.
Print Assumptions pas_false_correspondence.
Goal Logic.True. idtac "AUDIT_END pas_false_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pas_neq_correspondence". exact Logic.I. Qed.
Print Assumptions pas_neq_correspondence.
Goal Logic.True. idtac "AUDIT_END pas_neq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pas_valid_min_inter_arrival_related". exact Logic.I. Qed.
Print Assumptions pas_valid_min_inter_arrival_related.
Goal Logic.True. idtac "AUDIT_END pas_valid_min_inter_arrival_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pas_valid_taskset_related". exact Logic.I. Qed.
Print Assumptions pas_valid_taskset_related.
Goal Logic.True. idtac "AUDIT_END pas_valid_taskset_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pas_respects_sporadic_related". exact Logic.I. Qed.
Print Assumptions pas_respects_sporadic_related.
Goal Logic.True. idtac "AUDIT_END pas_respects_sporadic_related". exact Logic.I. Qed.
