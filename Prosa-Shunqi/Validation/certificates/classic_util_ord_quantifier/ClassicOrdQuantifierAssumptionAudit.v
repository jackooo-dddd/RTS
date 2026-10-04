From FoundationCertificates Require Import ClassicOrdQuantifierCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN exists_ord0_correspondence". exact Logic.I. Qed.
Print Assumptions exists_ord0_correspondence.
Goal Logic.True. idtac "AUDIT_END exists_ord0_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN exists_recr_correspondence". exact Logic.I. Qed.
Print Assumptions exists_recr_correspondence.
Goal Logic.True. idtac "AUDIT_END exists_recr_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN forall_ord0_correspondence". exact Logic.I. Qed.
Print Assumptions forall_ord0_correspondence.
Goal Logic.True. idtac "AUDIT_END forall_ord0_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN forall_recr_correspondence". exact Logic.I. Qed.
Print Assumptions forall_recr_correspondence.
Goal Logic.True. idtac "AUDIT_END forall_recr_correspondence". exact Logic.I. Qed.
