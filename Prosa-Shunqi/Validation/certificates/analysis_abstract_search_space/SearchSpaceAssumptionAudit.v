From FoundationCertificates Require Import
  SearchSpaceDefinitionsCorrespondence
  SearchSpaceRepresentativeCorrespondence
  SearchSpaceSolutionCorrespondence
  SearchSpaceSwitchCorrespondence.

Goal True.
Proof.
  idtac "AUDIT_BEGIN are_equivalent_at_values_less_than".
  Print Assumptions ss_equivalent_correspondence.
  idtac "AUDIT_END are_equivalent_at_values_less_than".
  idtac "AUDIT_BEGIN are_not_equivalent_at_values_less_than".
  Print Assumptions ss_not_equivalent_correspondence.
  idtac "AUDIT_END are_not_equivalent_at_values_less_than".
  idtac "AUDIT_BEGIN is_in_search_space".
  Print Assumptions ss_search_space_correspondence.
  idtac "AUDIT_END is_in_search_space".
  idtac "AUDIT_BEGIN representative_exists".
  Print Assumptions ss_representative_statement_correspondence.
  idtac "AUDIT_END representative_exists".
  idtac "AUDIT_BEGIN solution_for_A_exists".
  Print Assumptions ss_solution_statement_correspondence.
  idtac "AUDIT_END solution_for_A_exists".
  idtac "AUDIT_BEGIN search_space_switch_IBF".
  Print Assumptions ss_switch_statement_correspondence.
  idtac "AUDIT_END search_space_switch_IBF".
Abort.
