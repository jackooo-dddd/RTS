From FoundationCertificates Require Import LcmseqCertificate LcmseqTypeAudit.

Goal True. idtac "AUDIT_BEGIN int_divides". exact I. Qed.
Print Assumptions lcmt_int_divides_certificate.
Goal True. idtac "AUDIT_END int_divides". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN super_divides". exact I. Qed.
Print Assumptions lcmt_super_divides_certificate.
Goal True. idtac "AUDIT_END super_divides". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN member_divides". exact I. Qed.
Print Assumptions lcmt_member_divides_certificate.
Goal True. idtac "AUDIT_END member_divides". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN all_pos". exact I. Qed.
Print Assumptions lcmt_all_pos_certificate.
Goal True. idtac "AUDIT_END all_pos". exact I. Qed.
