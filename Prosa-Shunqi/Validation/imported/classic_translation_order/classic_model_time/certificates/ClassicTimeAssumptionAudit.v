From FoundationCertificates Require Import ClassicTimeCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN Time_time_rocq_roundtrip_certificate". exact Logic.I. Qed.
Print Assumptions Time_time_rocq_roundtrip_certificate.
Goal Logic.True. idtac "AUDIT_END Time_time_rocq_roundtrip_certificate". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Time_time_imported_roundtrip_certificate". exact Logic.I. Qed.
Print Assumptions Time_time_imported_roundtrip_certificate.
Goal Logic.True. idtac "AUDIT_END Time_time_imported_roundtrip_certificate". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Time_duration_rocq_roundtrip_certificate". exact Logic.I. Qed.
Print Assumptions Time_duration_rocq_roundtrip_certificate.
Goal Logic.True. idtac "AUDIT_END Time_duration_rocq_roundtrip_certificate". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Time_duration_imported_roundtrip_certificate". exact Logic.I. Qed.
Print Assumptions Time_duration_imported_roundtrip_certificate.
Goal Logic.True. idtac "AUDIT_END Time_duration_imported_roundtrip_certificate". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Time_instant_rocq_roundtrip_certificate". exact Logic.I. Qed.
Print Assumptions Time_instant_rocq_roundtrip_certificate.
Goal Logic.True. idtac "AUDIT_END Time_instant_rocq_roundtrip_certificate". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Time_instant_imported_roundtrip_certificate". exact Logic.I. Qed.
Print Assumptions Time_instant_imported_roundtrip_certificate.
Goal Logic.True. idtac "AUDIT_END Time_instant_imported_roundtrip_certificate". exact Logic.I. Qed.
