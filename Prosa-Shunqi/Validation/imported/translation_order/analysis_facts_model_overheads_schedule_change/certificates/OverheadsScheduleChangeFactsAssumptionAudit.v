From FoundationCertificates Require Import
  OvhArrivalsSeqBaseAdapter OvhArrivalsSeqOperations OvhArrivalsSeqCorrespondence OvhArrivalsCorrespondence OvhJitterSvcBaseAdapter OvhJitterSvcNatBoolOperations OvhJitterSvcIntervalOperations OvhJitterSvcScheduleOperations OvhJitterSvcJobOperations OvhPreemptionParameterCorrespondence OvhPreemptionTimeCorrespondence OvhPriorityDrivenCorrespondence OvhPStateCoverHelpers OvhFactsPreemptionHelpers OvhWorkloadCorrespondence OvhPriorityInversionCorrespondence OvhExistenceHelpers OvhHepAtPtHelpers OvhTaskPreemptionParametersCorrespondence OvhBusyIntervalPiHelpers OvhStateRel ScheduleChangeBaseAdapter ScheduleChangeStateAdapter ScheduleChangeOptionOperations ScheduleChangeIntervalOperations ScheduleChangeListOperations ScheduleChangeCorrespondence OverheadsScheduleChangeFactsCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN number_schedule_changes_cat_correspondence". exact Logic.I. Qed.
Print Assumptions number_schedule_changes_cat_correspondence.
Goal Logic.True. idtac "AUDIT_END number_schedule_changes_cat_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN first_schedule_change_exists_correspondence". exact Logic.I. Qed.
Print Assumptions first_schedule_change_exists_correspondence.
Goal Logic.True. idtac "AUDIT_END first_schedule_change_exists_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN number_schedule_changes_widen_correspondence". exact Logic.I. Qed.
Print Assumptions number_schedule_changes_widen_correspondence.
Goal Logic.True. idtac "AUDIT_END number_schedule_changes_widen_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN same_scheduled_state_merge_correspondence". exact Logic.I. Qed.
Print Assumptions same_scheduled_state_merge_correspondence.
Goal Logic.True. idtac "AUDIT_END same_scheduled_state_merge_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN no_schedule_changes_implies_constant_schedule_correspondence". exact Logic.I. Qed.
Print Assumptions no_schedule_changes_implies_constant_schedule_correspondence.
Goal Logic.True. idtac "AUDIT_END no_schedule_changes_implies_constant_schedule_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN no_changes_implies_same_scheduled_job_correspondence". exact Logic.I. Qed.
Print Assumptions no_changes_implies_same_scheduled_job_correspondence.
Goal Logic.True. idtac "AUDIT_END no_changes_implies_same_scheduled_job_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ovhsc_state_maps_agree". exact Logic.I. Qed.
Print Assumptions ovhsc_state_maps_agree.
Goal Logic.True. idtac "AUDIT_END ovhsc_state_maps_agree". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ovhsc_sched_rel". exact Logic.I. Qed.
Print Assumptions ovhsc_sched_rel.
Goal Logic.True. idtac "AUDIT_END ovhsc_sched_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ovhsc_forall_option". exact Logic.I. Qed.
Print Assumptions ovhsc_forall_option.
Goal Logic.True. idtac "AUDIT_END ovhsc_forall_option". exact Logic.I. Qed.
