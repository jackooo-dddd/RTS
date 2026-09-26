From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence IdealUniSchedulerCorrespondence EdfDefinitionsHelpers EdfDefinitionsCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN EDF_schedule_implies_respects_policy_at_preemption_point_correspondence". exact Logic.I. Qed.
Print Assumptions EDF_schedule_implies_respects_policy_at_preemption_point_correspondence.
Goal Logic.True. idtac "AUDIT_END EDF_schedule_implies_respects_policy_at_preemption_point_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN respects_policy_at_preemption_point_implies_EDF_schedule_correspondence". exact Logic.I. Qed.
Print Assumptions respects_policy_at_preemption_point_implies_EDF_schedule_correspondence.
Goal Logic.True. idtac "AUDIT_END respects_policy_at_preemption_point_implies_EDF_schedule_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN EDF_schedule_equiv_correspondence". exact Logic.I. Qed.
Print Assumptions EDF_schedule_equiv_correspondence.
Goal Logic.True. idtac "AUDIT_END EDF_schedule_equiv_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN edfd_ready_related". exact Logic.I. Qed.
Print Assumptions edfd_ready_related.
Goal Logic.True. idtac "AUDIT_END edfd_ready_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN edfd_preemptable_related". exact Logic.I. Qed.
Print Assumptions edfd_preemptable_related.
Goal Logic.True. idtac "AUDIT_END edfd_preemptable_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN edfd_jobs_must_arrive_rel". exact Logic.I. Qed.
Print Assumptions edfd_jobs_must_arrive_rel.
Goal Logic.True. idtac "AUDIT_END edfd_jobs_must_arrive_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN edfd_completed_jobs_dont_execute_rel". exact Logic.I. Qed.
Print Assumptions edfd_completed_jobs_dont_execute_rel.
Goal Logic.True. idtac "AUDIT_END edfd_completed_jobs_dont_execute_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN edfd_deadlines_met_rel". exact Logic.I. Qed.
Print Assumptions edfd_deadlines_met_rel.
Goal Logic.True. idtac "AUDIT_END edfd_deadlines_met_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN edfd_EDF_schedule_rel". exact Logic.I. Qed.
Print Assumptions edfd_EDF_schedule_rel.
Goal Logic.True. idtac "AUDIT_END edfd_EDF_schedule_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN edfd_respects_rel". exact Logic.I. Qed.
Print Assumptions edfd_respects_rel.
Goal Logic.True. idtac "AUDIT_END edfd_respects_rel". exact Logic.I. Qed.
