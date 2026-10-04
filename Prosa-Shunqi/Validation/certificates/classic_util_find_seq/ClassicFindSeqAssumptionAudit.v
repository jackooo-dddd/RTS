From FoundationCertificates Require Import ClassicFindSeqCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN findP_correspondence". exact Logic.I. Qed.
Print Assumptions findP_correspondence.
Goal Logic.True. idtac "AUDIT_END findP_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN findP_FIFO_correspondence". exact Logic.I. Qed.
Print Assumptions findP_FIFO_correspondence.
Goal Logic.True. idtac "AUDIT_END findP_FIFO_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN find_uniql_correspondence". exact Logic.I. Qed.
Print Assumptions find_uniql_correspondence.
Goal Logic.True. idtac "AUDIT_END find_uniql_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN find_uniq_correspondence". exact Logic.I. Qed.
Print Assumptions find_uniq_correspondence.
Goal Logic.True. idtac "AUDIT_END find_uniq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN findP_in_seq_correspondence". exact Logic.I. Qed.
Print Assumptions findP_in_seq_correspondence.
Goal Logic.True. idtac "AUDIT_END findP_in_seq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN findP_notSome_in_seq_correspondence". exact Logic.I. Qed.
Print Assumptions findP_notSome_in_seq_correspondence.
Goal Logic.True. idtac "AUDIT_END findP_notSome_in_seq_correspondence". exact Logic.I. Qed.
