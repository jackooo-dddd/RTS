From FoundationCertificates Require Import
  ArrivalSequenceBaseAdapter ArrivalSequenceOperations ArrivalSequenceCorrespondence SupplyScheduleBaseAdapter SupplyScheduleFiniteOperations SupplyScheduleOperations SupplyBaseAdapter SupplyNatBoolOperations SupplyIntervalOperations SupplyCorrespondence PredCorrespondence AbstractDefinitionsBaseAdapter ServiceBaseAdapter ServiceNatBoolOperations ServiceIntervalOperations ServiceScheduleOperations AbstractDefinitionsClasses AbstractDefinitionsTaskOperations AbstractDefinitionsBusyInterval BusySbfCorrespondence.

Goal Logic.True. idtac "AUDIT_BEGIN sbf_respected_in_busy_interval_correspondence". exact Logic.I. Qed.
Print Assumptions sbf_respected_in_busy_interval_correspondence.
Goal Logic.True. idtac "AUDIT_END sbf_respected_in_busy_interval_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN valid_busy_sbf_correspondence". exact Logic.I. Qed.
Print Assumptions valid_busy_sbf_correspondence.
Goal Logic.True. idtac "AUDIT_END valid_busy_sbf_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN busy_pred_related". exact Logic.I. Qed.
Print Assumptions busy_pred_related.
Goal Logic.True. idtac "AUDIT_END busy_pred_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pred_sbf_respected_correspondence". exact Logic.I. Qed.
Print Assumptions pred_sbf_respected_correspondence.
Goal Logic.True. idtac "AUDIT_END pred_sbf_respected_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pred_valid_pred_sbf_correspondence". exact Logic.I. Qed.
Print Assumptions pred_valid_pred_sbf_correspondence.
Goal Logic.True. idtac "AUDIT_END pred_valid_pred_sbf_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ad_busy_interval_prefix_correspondence". exact Logic.I. Qed.
Print Assumptions ad_busy_interval_prefix_correspondence.
Goal Logic.True. idtac "AUDIT_END ad_busy_interval_prefix_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ad_job_of_task_related". exact Logic.I. Qed.
Print Assumptions ad_job_of_task_related.
Goal Logic.True. idtac "AUDIT_END ad_job_of_task_related". exact Logic.I. Qed.
