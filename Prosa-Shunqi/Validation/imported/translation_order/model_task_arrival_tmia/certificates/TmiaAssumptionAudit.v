From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence TmiaCorrespondence.

Goal Logic.True. idtac "AUDIT_BEGIN TaskMaxInterArrival_source_total". exact Logic.I. Qed.
Print Assumptions TaskMaxInterArrival_source_total.
Goal Logic.True. idtac "AUDIT_END TaskMaxInterArrival_source_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN TaskMaxInterArrival_target_total". exact Logic.I. Qed.
Print Assumptions TaskMaxInterArrival_target_total.
Goal Logic.True. idtac "AUDIT_END TaskMaxInterArrival_target_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN positive_task_max_inter_arrival_time_correspondence". exact Logic.I. Qed.
Print Assumptions positive_task_max_inter_arrival_time_correspondence.
Goal Logic.True. idtac "AUDIT_END positive_task_max_inter_arrival_time_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arr_sep_task_max_inter_arrival_correspondence". exact Logic.I. Qed.
Print Assumptions arr_sep_task_max_inter_arrival_correspondence.
Goal Logic.True. idtac "AUDIT_END arr_sep_task_max_inter_arrival_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN valid_task_max_inter_arrival_time_correspondence". exact Logic.I. Qed.
Print Assumptions valid_task_max_inter_arrival_time_correspondence.
Goal Logic.True. idtac "AUDIT_END valid_task_max_inter_arrival_time_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN taskset_respects_task_max_inter_arrival_model_correspondence". exact Logic.I. Qed.
Print Assumptions taskset_respects_task_max_inter_arrival_model_correspondence.
Goal Logic.True. idtac "AUDIT_END taskset_respects_task_max_inter_arrival_model_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN tm_eq_correspondence". exact Logic.I. Qed.
Print Assumptions tm_eq_correspondence.
Goal Logic.True. idtac "AUDIT_END tm_eq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN tm_neq_correspondence". exact Logic.I. Qed.
Print Assumptions tm_neq_correspondence.
Goal Logic.True. idtac "AUDIT_END tm_neq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN tm_exists_id_correspondence". exact Logic.I. Qed.
Print Assumptions tm_exists_id_correspondence.
Goal Logic.True. idtac "AUDIT_END tm_exists_id_correspondence". exact Logic.I. Qed.
