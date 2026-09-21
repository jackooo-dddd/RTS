From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation EqTypeCorrespondence
  RelListCorrespondence SeqsetCorrespondence
  SubadditivityNatCorrespondence SupremumTheoremCorrespondence
  TacticsClosureCertificate RelClosureCertificate SeqsetClosureCertificate
  SubadditivityClosureCertificate SupremumClosureCertificate.

Goal True. idtac "AUDIT_BEGIN neqP". exact I. Qed.
Print Assumptions neqP_statement_correspondence_certificate.
Goal True. idtac "AUDIT_END neqP". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN total_over_list". exact I. Qed.
Print Assumptions total_over_list_correspondence_certificate.
Goal True. idtac "AUDIT_END total_over_list". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN antisymmetric_over_list". exact I. Qed.
Print Assumptions antisymmetric_over_list_correspondence_certificate.
Goal True. idtac "AUDIT_END antisymmetric_over_list". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN seqset_set". exact I. Qed.
Print Assumptions seqset_set_correspondence_certificate.
Goal True. idtac "AUDIT_END seqset_set". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN seqset_set_of". exact I. Qed.
Print Assumptions seqset_set_of_correspondence_certificate.
Goal True. idtac "AUDIT_END seqset_set_of". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN seqset_set_uniq". exact I. Qed.
Print Assumptions seqset_set_uniq_statement_correspondence_certificate.
Goal True. idtac "AUDIT_END seqset_set_uniq". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN subadditive_at". exact I. Qed.
Print Assumptions subadditive_at_correspondence_certificate.
Goal True. idtac "AUDIT_END subadditive_at". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN subadditive_until". exact I. Qed.
Print Assumptions subadditive_until_correspondence_certificate.
Goal True. idtac "AUDIT_END subadditive_until". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN subadditive". exact I. Qed.
Print Assumptions subadditive_correspondence_certificate.
Goal True. idtac "AUDIT_END subadditive". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN subadditive_standard". exact I. Qed.
Print Assumptions subadditive_standard_correspondence_certificate.
Goal True. idtac "AUDIT_END subadditive_standard". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN subadditive_standard_equivalence". exact I. Qed.
Print Assumptions subadditive_standard_equivalence_statement_certificate.
Goal True. idtac "AUDIT_END subadditive_standard_equivalence". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN subadditive_leq_mul". exact I. Qed.
Print Assumptions subadditive_leq_mul_statement_certificate.
Goal True. idtac "AUDIT_END subadditive_leq_mul". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN supremum_unfold". exact I. Qed.
Print Assumptions supremum_unfold_statement_correspondence_certificate.
Goal True. idtac "AUDIT_END supremum_unfold". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN supremum_exists". exact I. Qed.
Print Assumptions supremum_exists_statement_correspondence_certificate.
Goal True. idtac "AUDIT_END supremum_exists". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN supremum_none". exact I. Qed.
Print Assumptions supremum_none_statement_correspondence_certificate.
Goal True. idtac "AUDIT_END supremum_none". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN supremum_in". exact I. Qed.
Print Assumptions supremum_in_statement_correspondence_certificate.
Goal True. idtac "AUDIT_END supremum_in". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN supremum_spec". exact I. Qed.
Print Assumptions supremum_spec_statement_correspondence_certificate.
Goal True. idtac "AUDIT_END supremum_spec". exact I. Qed.

(** Independently audit the reusable bridge surface used by the targets. *)
Goal True. idtac "AUDIT_BEGIN common_eqtype_equality". exact I. Qed.
Print Assumptions eqtype_equality_observation_certificate.
Goal True. idtac "AUDIT_END common_eqtype_equality". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN common_eqtype_disequality". exact I. Qed.
Print Assumptions eqtype_disequality_observation_certificate.
Goal True. idtac "AUDIT_END common_eqtype_disequality". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN common_rel_membership". exact I. Qed.
Print Assumptions rel_membership_correspondence.
Goal True. idtac "AUDIT_END common_rel_membership". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN common_rel_bool". exact I. Qed.
Print Assumptions rel_bool_true_correspondence.
Goal True. idtac "AUDIT_END common_rel_bool". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN common_seqset_relation". exact I. Qed.
Print Assumptions seqset_relation_source_total.
Goal True. idtac "AUDIT_END common_seqset_relation". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN common_seqset_source_roundtrip". exact I. Qed.
Print Assumptions seqset_source_roundtrip_observable.
Goal True. idtac "AUDIT_END common_seqset_source_roundtrip". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN common_seqset_target_roundtrip". exact I. Qed.
Print Assumptions seqset_imported_roundtrip_observable.
Goal True. idtac "AUDIT_END common_seqset_target_roundtrip". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN common_nat_roundtrip". exact I. Qed.
Print Assumptions sub_nat_imported_roundtrip.
Goal True. idtac "AUDIT_END common_nat_roundtrip". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN common_nat_add". exact I. Qed.
Print Assumptions sub_add_correspondence.
Goal True. idtac "AUDIT_END common_nat_add". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN common_nat_mul". exact I. Qed.
Print Assumptions sub_mul_correspondence.
Goal True. idtac "AUDIT_END common_nat_mul". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN common_nat_le". exact I. Qed.
Print Assumptions sub_nat_le_correspondence.
Goal True. idtac "AUDIT_END common_nat_le". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN common_nat_lt". exact I. Qed.
Print Assumptions sub_nat_lt_correspondence.
Goal True. idtac "AUDIT_END common_nat_lt". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN common_nat_eq". exact I. Qed.
Print Assumptions sub_nat_eq_correspondence.
Goal True. idtac "AUDIT_END common_nat_eq". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN common_sup_bool". exact I. Qed.
Print Assumptions sup_bool_true_correspondence.
Goal True. idtac "AUDIT_END common_sup_bool". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN common_sup_or". exact I. Qed.
Print Assumptions sup_bool_or_correspondence.
Goal True. idtac "AUDIT_END common_sup_or". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN common_sup_membership". exact I. Qed.
Print Assumptions sup_membership_correspondence.
Goal True. idtac "AUDIT_END common_sup_membership". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN common_sup_option_eq". exact I. Qed.
Print Assumptions sup_option_eq_correspondence.
Goal True. idtac "AUDIT_END common_sup_option_eq". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN common_sup_list_eq". exact I. Qed.
Print Assumptions sup_list_eq_correspondence.
Goal True. idtac "AUDIT_END common_sup_list_eq". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN common_sup_option_ne". exact I. Qed.
Print Assumptions sup_option_ne_correspondence.
Goal True. idtac "AUDIT_END common_sup_option_ne". exact I. Qed.
