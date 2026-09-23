From FoundationCertificates Require Import SuperadditivityBaseCorrespondence
  SuperadditivityEquivalenceCertificate SuperadditivityArithmeticCertificate
  SuperadditivityMonotoneCertificate SuperadditivityExtensionOperations
  SuperadditivityHorizonCertificate.

Goal True. idtac "AUDIT_BEGIN superadditive_at". exact I. Qed.
Print Assumptions superadditive_at_correspondence.
Goal True. idtac "AUDIT_END superadditive_at". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN superadditive_until". exact I. Qed.
Print Assumptions superadditive_until_correspondence.
Goal True. idtac "AUDIT_END superadditive_until". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN superadditive". exact I. Qed.
Print Assumptions superadditive_correspondence.
Goal True. idtac "AUDIT_END superadditive". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN superadditive_standard". exact I. Qed.
Print Assumptions superadditive_standard_correspondence.
Goal True. idtac "AUDIT_END superadditive_standard". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN superadditive_standard_equivalence". exact I. Qed.
Print Assumptions superadditivity_equivalence_statement_certificate.
Goal True. idtac "AUDIT_END superadditive_standard_equivalence". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN superadditive_first_zero". exact I. Qed.
Print Assumptions superadditivity_first_zero_statement_certificate.
Goal True. idtac "AUDIT_END superadditive_first_zero". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN superadditive_leq_mul". exact I. Qed.
Print Assumptions superadditivity_leq_mul_statement_certificate.
Goal True. idtac "AUDIT_END superadditive_leq_mul". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN superadditive_unbounded". exact I. Qed.
Print Assumptions superadditivity_unbounded_statement_certificate.
Goal True. idtac "AUDIT_END superadditive_unbounded". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN superadditive_monotone". exact I. Qed.
Print Assumptions superadditivity_monotone_statement_certificate.
Goal True. idtac "AUDIT_END superadditive_monotone". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN minimal_superadditive_extension". exact I. Qed.
Print Assumptions sa_minimal_extension_related.
Goal True. idtac "AUDIT_END minimal_superadditive_extension". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN minimal_extension_superadditive_at_horizon". exact I. Qed.
Print Assumptions sa_horizon_at_statement_certificate.
Goal True. idtac "AUDIT_END minimal_extension_superadditive_at_horizon". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN minimal_extension_superadditive_until". exact I. Qed.
Print Assumptions sa_horizon_until_statement_certificate.
Goal True. idtac "AUDIT_END minimal_extension_superadditive_until". exact I. Qed.
