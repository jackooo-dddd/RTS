Require Import HardCoreCertificates HardNinRemAllCertificate
  HardStepFunctionCertificate FiniteNatSumBridge
  FiniteNatSumReuseCertificates.

Goal Logic.True. idtac "AUDIT_BEGIN rem_all". exact Logic.I. Qed.
Print Assumptions rem_all_recursive_certificate.
Goal Logic.True. idtac "AUDIT_BEGIN nin_rem_all". exact Logic.I. Qed.
Print Assumptions nin_rem_all_statement_certificate.
Goal Logic.True. idtac "AUDIT_BEGIN exists_first_intermediate_point". exact Logic.I. Qed.
Print Assumptions exists_first_intermediate_point_statement_certificate.
Goal Logic.True. idtac "AUDIT_BEGIN big_nat_eq0". exact Logic.I. Qed.
Print Assumptions big_nat_eq0_closed_certificate.
Goal Logic.True. idtac "AUDIT_BEGIN sum_of_ones". exact Logic.I. Qed.
Print Assumptions sum_of_ones_statement_certificate.
Goal Logic.True. idtac "AUDIT_BEGIN sum_le_summation_range". exact Logic.I. Qed.
Print Assumptions sum_le_summation_range_statement_certificate.
Goal Logic.True. idtac "AUDIT_BEGIN spin_idle". exact Logic.I. Qed.
Print Assumptions spin_idle_constructor_certificate.
Goal Logic.True. idtac "AUDIT_BEGIN spin_spin". exact Logic.I. Qed.
Print Assumptions spin_spin_constructor_certificate.
Goal Logic.True. idtac "AUDIT_BEGIN spin_progress". exact Logic.I. Qed.
Print Assumptions spin_progress_constructor_certificate.
Goal Logic.True. idtac "AUDIT_BEGIN spin_scheduled_on". exact Logic.I. Qed.
Print Assumptions spin_scheduled_on_certificate.
