From FoundationCertificates Require Import
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations ProgressCorrespondence.

Goal Logic.True. idtac "AUDIT_BEGIN job_has_progressed_correspondence". exact Logic.I. Qed.
Print Assumptions job_has_progressed_correspondence.
Goal Logic.True. idtac "AUDIT_END job_has_progressed_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN no_progress_correspondence". exact Logic.I. Qed.
Print Assumptions no_progress_correspondence.
Goal Logic.True. idtac "AUDIT_END no_progress_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN no_progress_equiv_correspondence". exact Logic.I. Qed.
Print Assumptions no_progress_equiv_correspondence.
Goal Logic.True. idtac "AUDIT_END no_progress_equiv_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN no_progress_for_correspondence". exact Logic.I. Qed.
Print Assumptions no_progress_for_correspondence.
Goal Logic.True. idtac "AUDIT_END no_progress_for_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pg_imp_correspondence". exact Logic.I. Qed.
Print Assumptions pg_imp_correspondence.
Goal Logic.True. idtac "AUDIT_END pg_imp_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pg_forall_nat_correspondence". exact Logic.I. Qed.
Print Assumptions pg_forall_nat_correspondence.
Goal Logic.True. idtac "AUDIT_END pg_forall_nat_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pg_forall_identity_correspondence". exact Logic.I. Qed.
Print Assumptions pg_forall_identity_correspondence.
Goal Logic.True. idtac "AUDIT_END pg_forall_identity_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pg_iff_correspondence". exact Logic.I. Qed.
Print Assumptions pg_iff_correspondence.
Goal Logic.True. idtac "AUDIT_END pg_iff_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pg_service_at_related". exact Logic.I. Qed.
Print Assumptions pg_service_at_related.
Goal Logic.True. idtac "AUDIT_END pg_service_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pg_service_related". exact Logic.I. Qed.
Print Assumptions pg_service_related.
Goal Logic.True. idtac "AUDIT_END pg_service_related". exact Logic.I. Qed.
