From FoundationCertificates Require Import WorkConservingCorrespondence.

Goal Logic.True.
Proof. idtac "AUDIT_BEGIN work_conserving". exact I. Qed.
Print Assumptions work_conserving_correspondence.
Goal Logic.True.
Proof. idtac "AUDIT_END work_conserving". exact I. Qed.

Goal Logic.True.
Proof. idtac "AUDIT_BEGIN jobs_backlogged_at". exact I. Qed.
Print Assumptions jobs_backlogged_at_correspondence.
Goal Logic.True.
Proof. idtac "AUDIT_END jobs_backlogged_at". exact I. Qed.
