Require Import FiniteNatSumBridge FiniteNatSumReuseCertificates.
Require Import JobArrivalCleanCertificate.
Require Import CompletesAtSemanticCertificate CompletesAtGenericCertificate.

Goal Logic.True. idtac "AUDIT_BEGIN big_nat_eq0". exact Logic.I. Qed.
Print big_nat_eq0_closed_certificate.
Print Assumptions big_nat_eq0_closed_certificate.
Goal Logic.True. idtac "AUDIT_END big_nat_eq0". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sum_le_summation_range". exact Logic.I. Qed.
Print sum_le_summation_range_statement_certificate.
Print Assumptions sum_le_summation_range_statement_certificate.
Goal Logic.True. idtac "AUDIT_END sum_le_summation_range". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_arrival". exact Logic.I. Qed.
Print clean_job_arrival_target_roundtrip.
Print Assumptions clean_job_arrival_target_roundtrip.
Goal Logic.True. idtac "AUDIT_END job_arrival". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN completes_at_counterexample". exact Logic.I. Qed.
Print completes_at_current_counterexample_witness.
Print Assumptions completes_at_current_counterexample_witness.
Goal Logic.True. idtac "AUDIT_END completes_at_counterexample". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN completes_at_corrected". exact Logic.I. Qed.
Print completes_at_corrected_certificate.
Print Assumptions completes_at_corrected_certificate.
Goal Logic.True. idtac "AUDIT_END completes_at_corrected". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN completes_at_generic". exact Logic.I. Qed.
Print official_completes_at_conditional_certificate.
Print Assumptions official_completes_at_conditional_certificate.
Goal Logic.True. idtac "AUDIT_END completes_at_generic". exact Logic.I. Qed.
