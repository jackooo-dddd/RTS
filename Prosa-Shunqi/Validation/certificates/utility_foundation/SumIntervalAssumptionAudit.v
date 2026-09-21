From FoundationCertificates Require Import
  SumIntervalCorrespondence SumIntervalCertificate.

Goal True. idtac "AUDIT_BEGIN finite_nat_sum_value". exact I. Qed.
Print Assumptions finite_nat_sum_value_correspondence.
Goal True. idtac "AUDIT_END finite_nat_sum_value". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN sum_of_ones". exact I. Qed.
Print Assumptions sum_of_ones_statement_certificate.
Goal True. idtac "AUDIT_END sum_of_ones". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN big_nat_eq0". exact I. Qed.
Print Assumptions big_nat_eq0_statement_certificate.
Goal True. idtac "AUDIT_END big_nat_eq0". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN sum_le_summation_range". exact I. Qed.
Print Assumptions sum_le_summation_range_statement_certificate.
Goal True. idtac "AUDIT_END sum_le_summation_range". exact I. Qed.

