Require Import JobArrivalClassCertificate CompletesAtSemanticCertificate.

Goal Logic.True. idtac "AUDIT_BEGIN job_arrival_full_class". exact Logic.I. Qed.
Print Assumptions job_arrival_target_roundtrip.

Goal Logic.True. idtac "AUDIT_BEGIN completes_at_current_counterexample". exact Logic.I. Qed.
Print Assumptions completes_at_current_counterexample_witness.

Goal Logic.True. idtac "AUDIT_BEGIN completes_at_corrected". exact Logic.I. Qed.
Print Assumptions completes_at_corrected_certificate.
