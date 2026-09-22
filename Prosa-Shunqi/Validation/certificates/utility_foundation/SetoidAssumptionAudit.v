From FoundationCertificates Require Import SetoidCertificate SetoidTypeAudit.

Goal True. idtac "AUDIT_BEGIN leb". exact I. Qed.
Print Assumptions leb_constructor_correspondence_certificate.
Goal True. idtac "AUDIT_END leb". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN leb_eq". exact I. Qed.
Print Assumptions leb_eq_statement_certificate.
Goal True. idtac "AUDIT_END leb_eq". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN leqRW". exact I. Qed.
Print Assumptions leqRW_definition_type_certificate.
Goal True. idtac "AUDIT_END leqRW". exact I. Qed.
