From FoundationCertificates Require Import
  UnitGrowthCorrespondence UnitGrowthCertificate.

Goal True. idtac "AUDIT_BEGIN unit_growth_function". exact I. Qed.
Print Assumptions ug_unit_growth_correspondence.
Goal True. idtac "AUDIT_END unit_growth_function". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN unit_growth_function_k_steps_bounded". exact I. Qed.
Print Assumptions unit_growth_function_k_steps_bounded_statement_certificate.
Goal True. idtac "AUDIT_END unit_growth_function_k_steps_bounded". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN exists_intermediate_point". exact I. Qed.
Print Assumptions exists_intermediate_point_statement_certificate.
Goal True. idtac "AUDIT_END exists_intermediate_point". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN exists_intermediate_point_leq". exact I. Qed.
Print Assumptions exists_intermediate_point_leq_statement_certificate.
Goal True. idtac "AUDIT_END exists_intermediate_point_leq". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN exists_first_intermediate_point". exact I. Qed.
Print Assumptions exists_first_intermediate_point_statement_certificate.
Goal True. idtac "AUDIT_END exists_first_intermediate_point". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN slowed". exact I. Qed.
Print Assumptions ug_slowed_correspondence.
Goal True. idtac "AUDIT_END slowed". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN slowed_respects_pointwise_leq". exact I. Qed.
Print Assumptions slowed_respects_pointwise_leq_statement_certificate.
Goal True. idtac "AUDIT_END slowed_respects_pointwise_leq". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN slowed_is_unit_step". exact I. Qed.
Print Assumptions slowed_is_unit_step_statement_certificate.
Goal True. idtac "AUDIT_END slowed_is_unit_step". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN slowed_respects_monotone". exact I. Qed.
Print Assumptions slowed_respects_monotone_statement_certificate.
Goal True. idtac "AUDIT_END slowed_respects_monotone". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN slowed_never_exceeds". exact I. Qed.
Print Assumptions slowed_never_exceeds_statement_certificate.
Goal True. idtac "AUDIT_END slowed_never_exceeds". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN bound_preserved_under_slowed". exact I. Qed.
Print Assumptions bound_preserved_under_slowed_statement_certificate.
Goal True. idtac "AUDIT_END bound_preserved_under_slowed". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN slowed_subtraction_value_preservation". exact I. Qed.
Print Assumptions slowed_subtraction_value_preservation_statement_certificate.
Goal True. idtac "AUDIT_END slowed_subtraction_value_preservation". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN common_bool_true". exact I. Qed.
Print Assumptions ug_bool_true_correspondence.
Goal True. idtac "AUDIT_END common_bool_true". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN common_bool_false". exact I. Qed.
Print Assumptions ug_bool_false_correspondence.
Goal True. idtac "AUDIT_END common_bool_false". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN common_slowed". exact I. Qed.
Print Assumptions ug_slowed_correspondence.
Goal True. idtac "AUDIT_END common_slowed". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN common_monotone". exact I. Qed.
Print Assumptions ug_monotone_correspondence.
Goal True. idtac "AUDIT_END common_monotone". exact I. Qed.
