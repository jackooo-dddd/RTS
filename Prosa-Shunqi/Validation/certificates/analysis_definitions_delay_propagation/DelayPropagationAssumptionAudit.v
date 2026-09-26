From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence DelayPropagationCorrespondence.

Goal Logic.True. idtac "AUDIT_BEGIN valid_delay_propagation_mapping_correspondence". exact Logic.I. Qed.
Print Assumptions valid_delay_propagation_mapping_correspondence.
Goal Logic.True. idtac "AUDIT_END valid_delay_propagation_mapping_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN propagated_arrival_sequence_correspondence". exact Logic.I. Qed.
Print Assumptions propagated_arrival_sequence_correspondence.
Goal Logic.True. idtac "AUDIT_END propagated_arrival_sequence_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_mapping_uniq_correspondence". exact Logic.I. Qed.
Print Assumptions job_mapping_uniq_correspondence.
Goal Logic.True. idtac "AUDIT_END job_mapping_uniq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN valid_arr_seq_propagation_mapping_correspondence". exact Logic.I. Qed.
Print Assumptions valid_arr_seq_propagation_mapping_correspondence.
Goal Logic.True. idtac "AUDIT_END valid_arr_seq_propagation_mapping_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jitter_delay_mapping_valid_correspondence". exact Logic.I. Qed.
Print Assumptions jitter_delay_mapping_valid_correspondence.
Goal Logic.True. idtac "AUDIT_END jitter_delay_mapping_valid_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN release_sequence_correspondence". exact Logic.I. Qed.
Print Assumptions release_sequence_correspondence.
Goal Logic.True. idtac "AUDIT_END release_sequence_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jitter_arr_seq_mapping_valid_correspondence". exact Logic.I. Qed.
Print Assumptions jitter_arr_seq_mapping_valid_correspondence.
Goal Logic.True. idtac "AUDIT_END jitter_arr_seq_mapping_valid_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN dp_release_as_arrival_related". exact Logic.I. Qed.
Print Assumptions dp_release_as_arrival_related.
Goal Logic.True. idtac "AUDIT_END dp_release_as_arrival_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN dp_valid_jitter_bounds_related". exact Logic.I. Qed.
Print Assumptions dp_valid_jitter_bounds_related.
Goal Logic.True. idtac "AUDIT_END dp_valid_jitter_bounds_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN dp_flatten_map_related". exact Logic.I. Qed.
Print Assumptions dp_flatten_map_related.
Goal Logic.True. idtac "AUDIT_END dp_flatten_map_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN dp_decide_eq_related". exact Logic.I. Qed.
Print Assumptions dp_decide_eq_related.
Goal Logic.True. idtac "AUDIT_END dp_decide_eq_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN dp_and4_correspondence". exact Logic.I. Qed.
Print Assumptions dp_and4_correspondence.
Goal Logic.True. idtac "AUDIT_END dp_and4_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN dp_forall_list". exact Logic.I. Qed.
Print Assumptions dp_forall_list.
Goal Logic.True. idtac "AUDIT_END dp_forall_list". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN dp_forall_arrival_sequence". exact Logic.I. Qed.
Print Assumptions dp_forall_arrival_sequence.
Goal Logic.True. idtac "AUDIT_END dp_forall_arrival_sequence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN TaskJitter_source_total". exact Logic.I. Qed.
Print Assumptions TaskJitter_source_total.
Goal Logic.True. idtac "AUDIT_END TaskJitter_source_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN TaskJitter_target_total". exact Logic.I. Qed.
Print Assumptions TaskJitter_target_total.
Goal Logic.True. idtac "AUDIT_END TaskJitter_target_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN JobJitter_source_total". exact Logic.I. Qed.
Print Assumptions JobJitter_source_total.
Goal Logic.True. idtac "AUDIT_END JobJitter_source_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN JobJitter_target_total". exact Logic.I. Qed.
Print Assumptions JobJitter_target_total.
Goal Logic.True. idtac "AUDIT_END JobJitter_target_total". exact Logic.I. Qed.
