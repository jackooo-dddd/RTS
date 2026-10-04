From FoundationCertificates Require Import ClassicCountingCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN count_or_correspondence". exact Logic.I. Qed.
Print Assumptions count_or_correspondence.
Goal Logic.True. idtac "AUDIT_END count_or_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sub_in_count_correspondence". exact Logic.I. Qed.
Print Assumptions sub_in_count_correspondence.
Goal Logic.True. idtac "AUDIT_END sub_in_count_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN count_sub_uniqr_correspondence". exact Logic.I. Qed.
Print Assumptions count_sub_uniqr_correspondence.
Goal Logic.True. idtac "AUDIT_END count_sub_uniqr_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN count_pred_inj_correspondence". exact Logic.I. Qed.
Print Assumptions count_pred_inj_correspondence.
Goal Logic.True. idtac "AUDIT_END count_pred_inj_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN count_exists_correspondence". exact Logic.I. Qed.
Print Assumptions count_exists_correspondence.
Goal Logic.True. idtac "AUDIT_END count_exists_correspondence". exact Logic.I. Qed.
