From FoundationCertificates Require Import
  NatSubCorrespondence NatCertificate.

Goal True. idtac "AUDIT_BEGIN subnACA". exact I. Qed.
Print Assumptions subnACA_correspondence_certificate.
Goal True. idtac "AUDIT_END subnACA". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN leq_subRL_impl". exact I. Qed.
Print Assumptions leq_subRL_impl_correspondence_certificate.
Goal True. idtac "AUDIT_END leq_subRL_impl". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN common_nat_sub_canonical". exact I. Qed.
Print Assumptions nat_target_sub_canonical.
Goal True. idtac "AUDIT_END common_nat_sub_canonical". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN common_nat_sub". exact I. Qed.
Print Assumptions nat_target_sub_correspondence.
Goal True. idtac "AUDIT_END common_nat_sub". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN common_nat_sub_nontruncated". exact I. Qed.
Print Assumptions nat_target_sub_nontruncated.
Goal True. idtac "AUDIT_END common_nat_sub_nontruncated". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN common_nat_sub_truncated". exact I. Qed.
Print Assumptions nat_target_sub_truncated.
Goal True. idtac "AUDIT_END common_nat_sub_truncated". exact I. Qed.
