From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence PreemptionTimeCorrespondence PriorityDrivenCorrespondence PStateCoverHelpers FactsPreemptionHelpers NatSubCorrespondence PcoBaseAdapter PcoStaticOrder PcoDynamicOrder PriorityCoercionCorrespondence PriorityGelHelpers FactsPriorityGelCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN hep_job_priority_point_correspondence". exact Logic.I. Qed.
Print Assumptions hep_job_priority_point_correspondence.
Goal Logic.True. idtac "AUDIT_END hep_job_priority_point_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN hep_job_arrival_gel_correspondence". exact Logic.I. Qed.
Print Assumptions hep_job_arrival_gel_correspondence.
Goal Logic.True. idtac "AUDIT_END hep_job_arrival_gel_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN hep_job_arrives_before_correspondence". exact Logic.I. Qed.
Print Assumptions hep_job_arrives_before_correspondence.
Goal Logic.True. idtac "AUDIT_END hep_job_arrives_before_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN hep_job_arrives_after_zero_correspondence". exact Logic.I. Qed.
Print Assumptions hep_job_arrives_after_zero_correspondence.
Goal Logic.True. idtac "AUDIT_END hep_job_arrives_after_zero_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN GEL_respects_sequential_tasks_correspondence". exact Logic.I. Qed.
Print Assumptions GEL_respects_sequential_tasks_correspondence.
Goal Logic.True. idtac "AUDIT_END GEL_respects_sequential_tasks_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN GEL_implies_sequential_tasks_correspondence". exact Logic.I. Qed.
Print Assumptions GEL_implies_sequential_tasks_correspondence.
Goal Logic.True. idtac "AUDIT_END GEL_implies_sequential_tasks_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fgel_exists_identity". exact Logic.I. Qed.
Print Assumptions fgel_exists_identity.
Goal Logic.True. idtac "AUDIT_END fgel_exists_identity". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fgel_hep_related". exact Logic.I. Qed.
Print Assumptions fgel_hep_related.
Goal Logic.True. idtac "AUDIT_END fgel_hep_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fgel_jpp_related". exact Logic.I. Qed.
Print Assumptions fgel_jpp_related.
Goal Logic.True. idtac "AUDIT_END fgel_jpp_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fgel_pp_related". exact Logic.I. Qed.
Print Assumptions fgel_pp_related.
Goal Logic.True. idtac "AUDIT_END fgel_pp_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fgel_same_task_related". exact Logic.I. Qed.
Print Assumptions fgel_same_task_related.
Goal Logic.True. idtac "AUDIT_END fgel_same_task_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fgel_forall_job_cost". exact Logic.I. Qed.
Print Assumptions fgel_forall_job_cost.
Goal Logic.True. idtac "AUDIT_END fgel_forall_job_cost". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fgel_sequential_tasks_rel". exact Logic.I. Qed.
Print Assumptions fgel_sequential_tasks_rel.
Goal Logic.True. idtac "AUDIT_END fgel_sequential_tasks_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fgel_work_bearing_rel". exact Logic.I. Qed.
Print Assumptions fgel_work_bearing_rel.
Goal Logic.True. idtac "AUDIT_END fgel_work_bearing_rel". exact Logic.I. Qed.
