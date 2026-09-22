From FoundationCertificates Require Import
  NondecreasingCorrespondence NondecreasingSimpleCertificate
  NondecreasingTypeAudit.

Goal True. idtac "AUDIT_BEGIN nondecreasing_sequence". exact I. Qed.
Print Assumptions nondecreasing_sequence_definition_certificate.
Goal True. idtac "AUDIT_END nondecreasing_sequence". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN increasing_sequence". exact I. Qed.
Print Assumptions increasing_sequence_definition_certificate.
Goal True. idtac "AUDIT_END increasing_sequence". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN distances". exact I. Qed.
Print Assumptions distances_definition_certificate.
Goal True. idtac "AUDIT_END distances". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN iota_is_increasing_sequence". exact I. Qed.
Print Assumptions iota_is_increasing_sequence_correspondence_certificate.
Goal True. idtac "AUDIT_END iota_is_increasing_sequence". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN increasing_implies_nondecreasing". exact I. Qed.
Print Assumptions increasing_implies_nondecreasing_correspondence_certificate.
Goal True. idtac "AUDIT_END increasing_implies_nondecreasing". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN nondecreasing_sequence_cons". exact I. Qed.
Print Assumptions nondecreasing_sequence_cons_correspondence_certificate.
Goal True. idtac "AUDIT_END nondecreasing_sequence_cons". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN nondec_seq_zero_first". exact I. Qed.
Print Assumptions nondec_seq_zero_first_correspondence_certificate.
Goal True. idtac "AUDIT_END nondec_seq_zero_first". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN nondecreasing_sequence_2cons_leVeq". exact I. Qed.
Print Assumptions nondecreasing_sequence_2cons_leVeq_correspondence_certificate.
Goal True. idtac "AUDIT_END nondecreasing_sequence_2cons_leVeq". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN nondecreasing_sequence_cons_double". exact I. Qed.
Print Assumptions nondecreasing_sequence_cons_double_correspondence_certificate.
Goal True. idtac "AUDIT_END nondecreasing_sequence_cons_double". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN nondecreasing_sequence_add_min". exact I. Qed.
Print Assumptions nondecreasing_sequence_add_min_correspondence_certificate.
Goal True. idtac "AUDIT_END nondecreasing_sequence_add_min". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN nondecreasing_sequence_cons_min". exact I. Qed.
Print Assumptions nondecreasing_sequence_cons_min_correspondence_certificate.
Goal True. idtac "AUDIT_END nondecreasing_sequence_cons_min". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN nondecreasing_sequence_cons_smin". exact I. Qed.
Print Assumptions nondecreasing_sequence_cons_smin_correspondence_certificate.
Goal True. idtac "AUDIT_END nondecreasing_sequence_cons_smin". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN last_is_max_in_nondecreasing_seq". exact I. Qed.
Print Assumptions last_is_max_in_nondecreasing_seq_correspondence_certificate.
Goal True. idtac "AUDIT_END last_is_max_in_nondecreasing_seq". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN antidensity_of_nondecreasing_seq". exact I. Qed.
Print Assumptions antidensity_of_nondecreasing_seq_correspondence_certificate.
Goal True. idtac "AUDIT_END antidensity_of_nondecreasing_seq". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN belonging_to_segment_of_seq_is_total". exact I. Qed.
Print Assumptions belonging_to_segment_of_seq_is_total_correspondence_certificate.
Goal True. idtac "AUDIT_END belonging_to_segment_of_seq_is_total". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN distances_unfold_2cons". exact I. Qed.
Print Assumptions distances_unfold_2cons_correspondence_certificate.
Goal True. idtac "AUDIT_END distances_unfold_2cons". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN distances_unfold_2app_last". exact I. Qed.
Print Assumptions distances_unfold_2app_last_correspondence_certificate.
Goal True. idtac "AUDIT_END distances_unfold_2app_last". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN distances_unfold_1app_last". exact I. Qed.
Print Assumptions distances_unfold_1app_last_correspondence_certificate.
Goal True. idtac "AUDIT_END distances_unfold_1app_last". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN distance_between_neighboring_elements_le_max_distance_in_seq". exact I. Qed.
Print Assumptions distance_between_neighboring_elements_le_max_distance_in_seq_correspondence_certificate.
Goal True. idtac "AUDIT_END distance_between_neighboring_elements_le_max_distance_in_seq". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN max_distance_in_seq_le_last_element_of_seq". exact I. Qed.
Print Assumptions max_distance_in_seq_le_last_element_of_seq_correspondence_certificate.
Goal True. idtac "AUDIT_END max_distance_in_seq_le_last_element_of_seq". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN last_seq_minus_last_distance_seq". exact I. Qed.
Print Assumptions last_seq_minus_last_distance_seq_correspondence_certificate.
Goal True. idtac "AUDIT_END last_seq_minus_last_distance_seq". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN max_distance_in_nontrivial_seq_is_positive". exact I. Qed.
Print Assumptions max_distance_in_nontrivial_seq_is_positive_correspondence_certificate.
Goal True. idtac "AUDIT_END max_distance_in_nontrivial_seq_is_positive". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN domination_of_distances_implies_domination_of_seq". exact I. Qed.
Print Assumptions domination_of_distances_implies_domination_of_seq_correspondence_certificate.
Goal True. idtac "AUDIT_END domination_of_distances_implies_domination_of_seq". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN function_of_distances_is_correct". exact I. Qed.
Print Assumptions function_of_distances_is_correct_correspondence_certificate.
Goal True. idtac "AUDIT_END function_of_distances_is_correct". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN size_of_seq_of_distances". exact I. Qed.
Print Assumptions size_of_seq_of_distances_correspondence_certificate.
Goal True. idtac "AUDIT_END size_of_seq_of_distances". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN nodup_sort_2cons_eq". exact I. Qed.
Print Assumptions nodup_sort_2cons_eq_correspondence_certificate.
Goal True. idtac "AUDIT_END nodup_sort_2cons_eq". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN nodup_sort_2cons_lt". exact I. Qed.
Print Assumptions nodup_sort_2cons_lt_correspondence_certificate.
Goal True. idtac "AUDIT_END nodup_sort_2cons_lt". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN last0_undup". exact I. Qed.
Print Assumptions last0_undup_correspondence_certificate.
Goal True. idtac "AUDIT_END last0_undup". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN nondecreasing_sequence_undup". exact I. Qed.
Print Assumptions nondecreasing_sequence_undup_correspondence_certificate.
Goal True. idtac "AUDIT_END nondecreasing_sequence_undup". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN undup_nth_le". exact I. Qed.
Print Assumptions undup_nth_le_correspondence_certificate.
Goal True. idtac "AUDIT_END undup_nth_le". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN distances_positive_undup". exact I. Qed.
Print Assumptions distances_positive_undup_correspondence_certificate.
Goal True. idtac "AUDIT_END distances_positive_undup". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN distances_of_iota_epsilon". exact I. Qed.
Print Assumptions distances_of_iota_epsilon_correspondence_certificate.
Goal True. idtac "AUDIT_END distances_of_iota_epsilon". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN distances_iota_filtered". exact I. Qed.
Print Assumptions distances_iota_filtered_correspondence_certificate.
Goal True. idtac "AUDIT_END distances_iota_filtered". exact I. Qed.
