Require Import FiniteNatSumBridge FiniteNatSumReuseCertificates.

Goal Logic.True. idtac "AUDIT_BEGIN big_nat_eq0". exact Logic.I. Qed.
Print Assumptions big_nat_eq0_closed_certificate.

Goal Logic.True. idtac "AUDIT_BEGIN sum_of_ones". exact Logic.I. Qed.
Print Assumptions sum_of_ones_statement_certificate.

Goal Logic.True. idtac "AUDIT_BEGIN sum_le_summation_range". exact Logic.I. Qed.
Print Assumptions sum_le_summation_range_statement_certificate.
