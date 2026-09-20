From FoundationCertificates Require Import
  PropSPropFoundation NotationCertificate TacticsCertificate RelCertificate
  SupremumCertificate.

Goal True. idtac "AUDIT_BEGIN constant_value". exact I. Qed.
Print Assumptions constant_value_certificate.
Goal True. idtac "AUDIT_END constant_value". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN modusponens_statement". exact I. Qed.
Print Assumptions modusponens_statement_certificate.
Goal True. idtac "AUDIT_END modusponens_statement". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN monotone_correspondence". exact I. Qed.
Print Assumptions monotone_correspondence_certificate.
Goal True. idtac "AUDIT_END monotone_correspondence". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN choose_superior". exact I. Qed.
Print Assumptions choose_superior_correspondence_certificate.
Goal True. idtac "AUDIT_END choose_superior". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN supremum". exact I. Qed.
Print Assumptions supremum_correspondence_certificate.
Goal True. idtac "AUDIT_END supremum". exact I. Qed.
