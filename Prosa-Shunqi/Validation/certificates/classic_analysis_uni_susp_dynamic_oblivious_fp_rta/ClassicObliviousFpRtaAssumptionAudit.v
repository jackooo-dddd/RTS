From FoundationCertificates Require Import ClassicObliviousFpRtaCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN SuspensionObliviousFP_suspension_oblivious_fp_rta_implies_schedulability_correspondence". exact Logic.I. Qed.
Print Assumptions SuspensionObliviousFP_suspension_oblivious_fp_rta_implies_schedulability_correspondence.
Goal Logic.True. idtac "AUDIT_END SuspensionObliviousFP_suspension_oblivious_fp_rta_implies_schedulability_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cso_forall_sched". exact Logic.I. Qed.
Print Assumptions cso_forall_sched.
Goal Logic.True. idtac "AUDIT_END cso_forall_sched". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cso_forall_par". exact Logic.I. Qed.
Print Assumptions cso_forall_par.
Goal Logic.True. idtac "AUDIT_END cso_forall_par". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cso_forall_arr". exact Logic.I. Qed.
Print Assumptions cso_forall_arr.
Goal Logic.True. idtac "AUDIT_END cso_forall_arr". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cso_forall_susp". exact Logic.I. Qed.
Print Assumptions cso_forall_susp.
Goal Logic.True. idtac "AUDIT_END cso_forall_susp". exact Logic.I. Qed.
