From FoundationCertificates Require Import ClassicBuildSuspensionTableCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN SuspensionTableConstruction_build_suspension_duration_correspondence". exact Logic.I. Qed.
Print Assumptions SuspensionTableConstruction_build_suspension_duration_correspondence.
Goal Logic.True. idtac "AUDIT_END SuspensionTableConstruction_build_suspension_duration_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN SuspensionTableConstruction_not_suspended_before_suspension_start_correspondence". exact Logic.I. Qed.
Print Assumptions SuspensionTableConstruction_not_suspended_before_suspension_start_correspondence.
Goal Logic.True. idtac "AUDIT_END SuspensionTableConstruction_not_suspended_before_suspension_start_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN SuspensionTableConstruction_suspension_duration_no_suspension_after_t_max_correspondence". exact Logic.I. Qed.
Print Assumptions SuspensionTableConstruction_suspension_duration_no_suspension_after_t_max_correspondence.
Goal Logic.True. idtac "AUDIT_END SuspensionTableConstruction_suspension_duration_no_suspension_after_t_max_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN SuspensionTableConstruction_suspension_duration_matches_predicate_up_to_t_max_correspondence". exact Logic.I. Qed.
Print Assumptions SuspensionTableConstruction_suspension_duration_matches_predicate_up_to_t_max_correspondence.
Goal Logic.True. idtac "AUDIT_END SuspensionTableConstruction_suspension_duration_matches_predicate_up_to_t_max_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cbt_icof". exact Logic.I. Qed.
Print Assumptions cbt_icof.
Goal Logic.True. idtac "AUDIT_END cbt_icof". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cbt_forall_spred". exact Logic.I. Qed.
Print Assumptions cbt_forall_spred.
Goal Logic.True. idtac "AUDIT_END cbt_forall_spred". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cbt_forall_sched". exact Logic.I. Qed.
Print Assumptions cbt_forall_sched.
Goal Logic.True. idtac "AUDIT_END cbt_forall_sched". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cbt_forall_par". exact Logic.I. Qed.
Print Assumptions cbt_forall_par.
Goal Logic.True. idtac "AUDIT_END cbt_forall_par". exact Logic.I. Qed.
