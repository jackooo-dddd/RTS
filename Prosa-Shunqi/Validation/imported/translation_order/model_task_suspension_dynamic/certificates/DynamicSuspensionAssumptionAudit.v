From FoundationCertificates Require Import
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations ProgressHelpers SuspensionCorrespondence DynamicSuspensionCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN TaskTotalSuspension_source_total". exact Logic.I. Qed.
Print Assumptions TaskTotalSuspension_source_total.
Goal Logic.True. idtac "AUDIT_END TaskTotalSuspension_source_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN TaskTotalSuspension_target_total". exact Logic.I. Qed.
Print Assumptions TaskTotalSuspension_target_total.
Goal Logic.True. idtac "AUDIT_END TaskTotalSuspension_target_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN valid_dynamic_suspensions_correspondence". exact Logic.I. Qed.
Print Assumptions valid_dynamic_suspensions_correspondence.
Goal Logic.True. idtac "AUDIT_END valid_dynamic_suspensions_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN dsusp_lean_transport". exact Logic.I. Qed.
Print Assumptions dsusp_lean_transport.
Goal Logic.True. idtac "AUDIT_END dsusp_lean_transport". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN dsusp_job_task_import". exact Logic.I. Qed.
Print Assumptions dsusp_job_task_import.
Goal Logic.True. idtac "AUDIT_END dsusp_job_task_import". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN dsusp_job_task_export". exact Logic.I. Qed.
Print Assumptions dsusp_job_task_export.
Goal Logic.True. idtac "AUDIT_END dsusp_job_task_export". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN dsusp_task_bound_related". exact Logic.I. Qed.
Print Assumptions dsusp_task_bound_related.
Goal Logic.True. idtac "AUDIT_END dsusp_task_bound_related". exact Logic.I. Qed.
