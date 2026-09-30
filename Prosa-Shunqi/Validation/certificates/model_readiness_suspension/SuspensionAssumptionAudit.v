From FoundationCertificates Require Import
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations ProgressHelpers SuspensionCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN JobSuspension_source_total". exact Logic.I. Qed.
Print Assumptions JobSuspension_source_total.
Goal Logic.True. idtac "AUDIT_END JobSuspension_source_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN JobSuspension_target_total". exact Logic.I. Qed.
Print Assumptions JobSuspension_target_total.
Goal Logic.True. idtac "AUDIT_END JobSuspension_target_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN suspension_has_passed_correspondence". exact Logic.I. Qed.
Print Assumptions suspension_has_passed_correspondence.
Goal Logic.True. idtac "AUDIT_END suspension_has_passed_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN suspended_correspondence". exact Logic.I. Qed.
Print Assumptions suspended_correspondence.
Goal Logic.True. idtac "AUDIT_END suspended_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN total_suspension_correspondence". exact Logic.I. Qed.
Print Assumptions total_suspension_correspondence.
Goal Logic.True. idtac "AUDIT_END total_suspension_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN susp_nat_input". exact Logic.I. Qed.
Print Assumptions susp_nat_input.
Goal Logic.True. idtac "AUDIT_END susp_nat_input". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN susp_import_fun_rel". exact Logic.I. Qed.
Print Assumptions susp_import_fun_rel.
Goal Logic.True. idtac "AUDIT_END susp_import_fun_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN susp_export_fun_rel". exact Logic.I. Qed.
Print Assumptions susp_export_fun_rel.
Goal Logic.True. idtac "AUDIT_END susp_export_fun_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN susp_completed_by_related". exact Logic.I. Qed.
Print Assumptions susp_completed_by_related.
Goal Logic.True. idtac "AUDIT_END susp_completed_by_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN susp_pending_related". exact Logic.I. Qed.
Print Assumptions susp_pending_related.
Goal Logic.True. idtac "AUDIT_END susp_pending_related". exact Logic.I. Qed.
