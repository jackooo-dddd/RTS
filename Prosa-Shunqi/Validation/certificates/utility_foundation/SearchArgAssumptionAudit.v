From FoundationCertificates Require Import
  SearchArgDefinitionCertificate SearchArgStatementCertificate.

Goal True. idtac "AUDIT_BEGIN search_arg". exact I. Qed.
Print Assumptions search_arg_definition_certificate.
Goal True. idtac "AUDIT_END search_arg". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN earliest_pred_element_exists_case". exact I. Qed.
Print Assumptions earliest_pred_element_exists_case_statement_certificate.
Goal True. idtac "AUDIT_END earliest_pred_element_exists_case". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN search_arg_none". exact I. Qed.
Print Assumptions search_arg_none_statement_certificate.
Goal True. idtac "AUDIT_END search_arg_none". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN search_arg_not_none". exact I. Qed.
Print Assumptions search_arg_not_none_statement_certificate.
Goal True. idtac "AUDIT_END search_arg_not_none". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN search_arg_pred". exact I. Qed.
Print Assumptions search_arg_pred_statement_certificate.
Goal True. idtac "AUDIT_END search_arg_pred". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN search_arg_in_range". exact I. Qed.
Print Assumptions search_arg_in_range_statement_certificate.
Goal True. idtac "AUDIT_END search_arg_in_range". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN search_arg_extremum". exact I. Qed.
Print Assumptions search_arg_extremum_statement_certificate.
Goal True. idtac "AUDIT_END search_arg_extremum". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN prop_on_ex_minn". exact I. Qed.
Print Assumptions prop_on_ex_minn_statement_certificate.
Goal True. idtac "AUDIT_END prop_on_ex_minn". exact I. Qed.

