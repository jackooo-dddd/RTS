From FoundationCertificates Require Import
  OvhArrivalsSeqBaseAdapter OvhArrivalsSeqOperations OvhArrivalsSeqCorrespondence OvhArrivalsCorrespondence OvhJitterSvcBaseAdapter OvhJitterSvcNatBoolOperations OvhJitterSvcIntervalOperations OvhJitterSvcScheduleOperations OvhJitterSvcJobOperations OvhPreemptionParameterCorrespondence OvhPreemptionTimeCorrespondence OvhPriorityDrivenCorrespondence OvhPStateCoverHelpers OvhFactsPreemptionHelpers OvhWorkloadCorrespondence OvhPriorityInversionCorrespondence OvhExistenceHelpers OvhHepAtPtHelpers OvhTaskPreemptionParametersCorrespondence OvhBusyIntervalPiHelpers OvhStateRel OverheadsScheduleCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN overheads_proc_model_is_a_uniprocessor_model_correspondence". exact Logic.I. Qed.
Print Assumptions overheads_proc_model_is_a_uniprocessor_model_correspondence.
Goal Logic.True. idtac "AUDIT_END overheads_proc_model_is_a_uniprocessor_model_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN overheads_proc_model_provides_unit_supply_correspondence". exact Logic.I. Qed.
Print Assumptions overheads_proc_model_provides_unit_supply_correspondence.
Goal Logic.True. idtac "AUDIT_END overheads_proc_model_provides_unit_supply_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN overheads_proc_model_fully_consuming_correspondence". exact Logic.I. Qed.
Print Assumptions overheads_proc_model_fully_consuming_correspondence.
Goal Logic.True. idtac "AUDIT_END overheads_proc_model_fully_consuming_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN scheduled_job_dec_correspondence". exact Logic.I. Qed.
Print Assumptions scheduled_job_dec_correspondence.
Goal Logic.True. idtac "AUDIT_END scheduled_job_dec_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN scheduled_at_iff_scheduled_job_correspondence". exact Logic.I. Qed.
Print Assumptions scheduled_at_iff_scheduled_job_correspondence.
Goal Logic.True. idtac "AUDIT_END scheduled_at_iff_scheduled_job_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_scheduled_in_busy_interval_prefix_correspondence". exact Logic.I. Qed.
Print Assumptions job_scheduled_in_busy_interval_prefix_correspondence.
Goal Logic.True. idtac "AUDIT_END job_scheduled_in_busy_interval_prefix_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ovh_supply_at_related". exact Logic.I. Qed.
Print Assumptions ovh_supply_at_related.
Goal Logic.True. idtac "AUDIT_END ovh_supply_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ovh_opt_eq_correspondence". exact Logic.I. Qed.
Print Assumptions ovh_opt_eq_correspondence.
Goal Logic.True. idtac "AUDIT_END ovh_opt_eq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ovh_scheduled_job_related". exact Logic.I. Qed.
Print Assumptions ovh_scheduled_job_related.
Goal Logic.True. idtac "AUDIT_END ovh_scheduled_job_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ovh_forall_ja". exact Logic.I. Qed.
Print Assumptions ovh_forall_ja.
Goal Logic.True. idtac "AUDIT_END ovh_forall_ja". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ovh_forall_cost". exact Logic.I. Qed.
Print Assumptions ovh_forall_cost.
Goal Logic.True. idtac "AUDIT_END ovh_forall_cost". exact Logic.I. Qed.
