From FoundationCertificates Require Import ClassicInductionCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN strong_ind_correspondence". exact Logic.I. Qed.
Print Assumptions strong_ind_correspondence.
Goal Logic.True. idtac "AUDIT_END strong_ind_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN leq_as_delta_correspondence". exact Logic.I. Qed.
Print Assumptions leq_as_delta_correspondence.
Goal Logic.True. idtac "AUDIT_END leq_as_delta_correspondence". exact Logic.I. Qed.
