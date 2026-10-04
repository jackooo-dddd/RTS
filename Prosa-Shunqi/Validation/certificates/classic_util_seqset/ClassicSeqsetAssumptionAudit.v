From FoundationCertificates Require Import ClassicSeqsetCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN set_mem_correspondence". exact Logic.I. Qed.
Print Assumptions set_mem_correspondence.
Goal Logic.True. idtac "AUDIT_END set_mem_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN set_card_correspondence". exact Logic.I. Qed.
Print Assumptions set_card_correspondence.
Goal Logic.True. idtac "AUDIT_END set_card_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cs_seqset_target_total". exact Logic.I. Qed.
Print Assumptions cs_seqset_target_total.
Goal Logic.True. idtac "AUDIT_END cs_seqset_target_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cs_card_filter". exact Logic.I. Qed.
Print Assumptions cs_card_filter.
Goal Logic.True. idtac "AUDIT_END cs_card_filter". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cs_filter_rel". exact Logic.I. Qed.
Print Assumptions cs_filter_rel.
Goal Logic.True. idtac "AUDIT_END cs_filter_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cs_size_rel". exact Logic.I. Qed.
Print Assumptions cs_size_rel.
Goal Logic.True. idtac "AUDIT_END cs_size_rel". exact Logic.I. Qed.
