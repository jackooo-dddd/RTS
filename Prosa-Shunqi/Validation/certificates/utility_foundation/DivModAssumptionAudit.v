From FoundationCertificates Require Import DivModCertificate DivModTypeAudit.

Goal True. idtac "AUDIT_BEGIN eqdivn_leqmodn". exact I. Qed.
Print Assumptions eqdivn_leqmodn_statement_certificate.
Goal True. idtac "AUDIT_END eqdivn_leqmodn". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN ltdivn_dvdn". exact I. Qed.
Print Assumptions ltdivn_dvdn_statement_certificate.
Goal True. idtac "AUDIT_END ltdivn_dvdn". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN addn1_modn_commute". exact I. Qed.
Print Assumptions addn1_modn_commute_statement_certificate.
Goal True. idtac "AUDIT_END addn1_modn_commute". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN addmod_le_mod". exact I. Qed.
Print Assumptions addmod_le_mod_statement_certificate.
Goal True. idtac "AUDIT_END addmod_le_mod". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN divn_leq". exact I. Qed.
Print Assumptions divn_leq_statement_certificate.
Goal True. idtac "AUDIT_END divn_leq". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN div_floor". exact I. Qed.
Print Assumptions div_floor_definition_certificate.
Goal True. idtac "AUDIT_END div_floor". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN div_ceil". exact I. Qed.
Print Assumptions div_ceil_definition_certificate.
Goal True. idtac "AUDIT_END div_ceil". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN div_ceil0". exact I. Qed.
Print Assumptions div_ceil0_statement_certificate.
Goal True. idtac "AUDIT_END div_ceil0". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN div_ceil_gt0". exact I. Qed.
Print Assumptions div_ceil_gt0_statement_certificate.
Goal True. idtac "AUDIT_END div_ceil_gt0". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN div_ceil_monotone1". exact I. Qed.
Print Assumptions div_ceil_monotone1_statement_certificate.
Goal True. idtac "AUDIT_END div_ceil_monotone1". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN leq_div_ceil_add1". exact I. Qed.
Print Assumptions leq_div_ceil_add1_statement_certificate.
Goal True. idtac "AUDIT_END leq_div_ceil_add1". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN div_ceil_subadditive". exact I. Qed.
Print Assumptions div_ceil_subadditive_statement_certificate.
Goal True. idtac "AUDIT_END div_ceil_subadditive". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN div_ceil_multiple". exact I. Qed.
Print Assumptions div_ceil_multiple_statement_certificate.
Goal True. idtac "AUDIT_END div_ceil_multiple". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN div_floor_add_g". exact I. Qed.
Print Assumptions div_floor_add_g_statement_certificate.
Goal True. idtac "AUDIT_END div_floor_add_g". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN mod_elim". exact I. Qed.
Print Assumptions mod_elim_statement_certificate.
Goal True. idtac "AUDIT_END mod_elim". exact I. Qed.
