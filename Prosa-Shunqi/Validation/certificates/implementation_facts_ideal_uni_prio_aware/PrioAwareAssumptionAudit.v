From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence IdealUniSchedulerCorrespondence PreemptionAwareHelpers PrioAwareCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN uni_schedule_work_conserving_correspondence". exact Logic.I. Qed.
Print Assumptions uni_schedule_work_conserving_correspondence.
Goal Logic.True. idtac "AUDIT_END uni_schedule_work_conserving_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN uni_schedule_valid_correspondence". exact Logic.I. Qed.
Print Assumptions uni_schedule_valid_correspondence.
Goal Logic.True. idtac "AUDIT_END uni_schedule_valid_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN schedule_respects_preemption_model_correspondence". exact Logic.I. Qed.
Print Assumptions schedule_respects_preemption_model_correspondence.
Goal Logic.True. idtac "AUDIT_END schedule_respects_preemption_model_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN scheduled_job_is_supremum_correspondence". exact Logic.I. Qed.
Print Assumptions scheduled_job_is_supremum_correspondence.
Goal Logic.True. idtac "AUDIT_END scheduled_job_is_supremum_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN schedule_respects_policy_correspondence". exact Logic.I. Qed.
Print Assumptions schedule_respects_policy_correspondence.
Goal Logic.True. idtac "AUDIT_END schedule_respects_policy_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pr_jldp_to_target_rel". exact Logic.I. Qed.
Print Assumptions pr_jldp_to_target_rel.
Goal Logic.True. idtac "AUDIT_END pr_jldp_to_target_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pr_jldp_to_source_rel". exact Logic.I. Qed.
Print Assumptions pr_jldp_to_source_rel.
Goal Logic.True. idtac "AUDIT_END pr_jldp_to_source_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pr_forall_jldp". exact Logic.I. Qed.
Print Assumptions pr_forall_jldp.
Goal Logic.True. idtac "AUDIT_END pr_forall_jldp". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pr_uni_related". exact Logic.I. Qed.
Print Assumptions pr_uni_related.
Goal Logic.True. idtac "AUDIT_END pr_uni_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pr_choose_related". exact Logic.I. Qed.
Print Assumptions pr_choose_related.
Goal Logic.True. idtac "AUDIT_END pr_choose_related". exact Logic.I. Qed.
