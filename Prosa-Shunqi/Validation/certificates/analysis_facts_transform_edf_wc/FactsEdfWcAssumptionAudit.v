From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence IdealUniSchedulerCorrespondence EdfDefinitionsHelpers EdfTransCorrespondence FactsEdfOptCorrespondence FactsEdfWcCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN non_idle_swap_maintains_work_conservation_t1_correspondence". exact Logic.I. Qed.
Print Assumptions non_idle_swap_maintains_work_conservation_t1_correspondence.
Goal Logic.True. idtac "AUDIT_END non_idle_swap_maintains_work_conservation_t1_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN non_idle_swap_maintains_work_conservation_t2_correspondence". exact Logic.I. Qed.
Print Assumptions non_idle_swap_maintains_work_conservation_t2_correspondence.
Goal Logic.True. idtac "AUDIT_END non_idle_swap_maintains_work_conservation_t2_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN non_idle_swap_maintains_work_conservation_LEQ_t1_correspondence". exact Logic.I. Qed.
Print Assumptions non_idle_swap_maintains_work_conservation_LEQ_t1_correspondence.
Goal Logic.True. idtac "AUDIT_END non_idle_swap_maintains_work_conservation_LEQ_t1_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN non_idle_swap_maintains_work_conservation_GT_t2_correspondence". exact Logic.I. Qed.
Print Assumptions non_idle_swap_maintains_work_conservation_GT_t2_correspondence.
Goal Logic.True. idtac "AUDIT_END non_idle_swap_maintains_work_conservation_GT_t2_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN non_idle_swap_maintains_work_conservation_BET_t1_t2_correspondence". exact Logic.I. Qed.
Print Assumptions non_idle_swap_maintains_work_conservation_BET_t1_t2_correspondence.
Goal Logic.True. idtac "AUDIT_END non_idle_swap_maintains_work_conservation_BET_t1_t2_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsc_swap_maintains_work_conservation_correspondence". exact Logic.I. Qed.
Print Assumptions fsc_swap_maintains_work_conservation_correspondence.
Goal Logic.True. idtac "AUDIT_END fsc_swap_maintains_work_conservation_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN mea_maintains_work_conservation_correspondence". exact Logic.I. Qed.
Print Assumptions mea_maintains_work_conservation_correspondence.
Goal Logic.True. idtac "AUDIT_END mea_maintains_work_conservation_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN scheduled_behavior_premises_correspondence". exact Logic.I. Qed.
Print Assumptions scheduled_behavior_premises_correspondence.
Goal Logic.True. idtac "AUDIT_END scheduled_behavior_premises_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN edf_transform_prefix_maintains_work_conservation_correspondence". exact Logic.I. Qed.
Print Assumptions edf_transform_prefix_maintains_work_conservation_correspondence.
Goal Logic.True. idtac "AUDIT_END edf_transform_prefix_maintains_work_conservation_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sched_satisfies_behavior_premises_correspondence". exact Logic.I. Qed.
Print Assumptions sched_satisfies_behavior_premises_correspondence.
Goal Logic.True. idtac "AUDIT_END sched_satisfies_behavior_premises_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN edf_transform_maintains_work_conservation_correspondence". exact Logic.I. Qed.
Print Assumptions edf_transform_maintains_work_conservation_correspondence.
Goal Logic.True. idtac "AUDIT_END edf_transform_maintains_work_conservation_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN few_sched_at". exact Logic.I. Qed.
Print Assumptions few_sched_at.
Goal Logic.True. idtac "AUDIT_END few_sched_at". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN few_backlogged_related". exact Logic.I. Qed.
Print Assumptions few_backlogged_related.
Goal Logic.True. idtac "AUDIT_END few_backlogged_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN few_wc_rel". exact Logic.I. Qed.
Print Assumptions few_wc_rel.
Goal Logic.True. idtac "AUDIT_END few_wc_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN few_exists_sched". exact Logic.I. Qed.
Print Assumptions few_exists_sched.
Goal Logic.True. idtac "AUDIT_END few_exists_sched". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN few_swapped". exact Logic.I. Qed.
Print Assumptions few_swapped.
Goal Logic.True. idtac "AUDIT_END few_swapped". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN few_outer". exact Logic.I. Qed.
Print Assumptions few_outer.
Goal Logic.True. idtac "AUDIT_END few_outer". exact Logic.I. Qed.
