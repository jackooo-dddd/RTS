From FoundationCertificates Require Import
  NatSubCorrespondence LcmseqBaseAdapter LcmseqDivModAdapter LcmseqCorrespondence LcmseqCertificate LcmseqSpecCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN lcml_correspondence". exact Logic.I. Qed.
Print Assumptions lcml_correspondence.
Goal Logic.True. idtac "AUDIT_END lcml_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN int_divides_lcm_in_seq_correspondence". exact Logic.I. Qed.
Print Assumptions int_divides_lcm_in_seq_correspondence.
Goal Logic.True. idtac "AUDIT_END int_divides_lcm_in_seq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN lcm_seq_divides_lcm_super_correspondence". exact Logic.I. Qed.
Print Assumptions lcm_seq_divides_lcm_super_correspondence.
Goal Logic.True. idtac "AUDIT_END lcm_seq_divides_lcm_super_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN lcm_seq_is_mult_of_all_ints_correspondence". exact Logic.I. Qed.
Print Assumptions lcm_seq_is_mult_of_all_ints_correspondence.
Goal Logic.True. idtac "AUDIT_END lcm_seq_is_mult_of_all_ints_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN all_pos_implies_lcml_pos_correspondence". exact Logic.I. Qed.
Print Assumptions all_pos_implies_lcml_pos_correspondence.
Goal Logic.True. idtac "AUDIT_END all_pos_implies_lcml_pos_correspondence". exact Logic.I. Qed.
