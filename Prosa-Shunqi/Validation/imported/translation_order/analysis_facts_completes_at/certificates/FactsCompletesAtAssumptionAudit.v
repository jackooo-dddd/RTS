From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence PreemptionTimeCorrespondence PriorityDrivenCorrespondence PStateCoverHelpers BusyIntervalClassicalHelpers FactsCompletesAtCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN scheduled_at_precedes_completes_at_correspondence". exact Logic.I. Qed.
Print Assumptions scheduled_at_precedes_completes_at_correspondence.
Goal Logic.True. idtac "AUDIT_END scheduled_at_precedes_completes_at_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_completes_at_most_once_correspondence". exact Logic.I. Qed.
Print Assumptions job_completes_at_most_once_correspondence.
Goal Logic.True. idtac "AUDIT_END job_completes_at_most_once_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN only_one_job_completes_at_a_time_correspondence". exact Logic.I. Qed.
Print Assumptions only_one_job_completes_at_a_time_correspondence.
Goal Logic.True. idtac "AUDIT_END only_one_job_completes_at_a_time_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN completetion_time_is_preemption_time_correspondence". exact Logic.I. Qed.
Print Assumptions completetion_time_is_preemption_time_correspondence.
Goal Logic.True. idtac "AUDIT_END completetion_time_is_preemption_time_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN no_early_hep_job_completes_during_busy_prefix_correspondence". exact Logic.I. Qed.
Print Assumptions no_early_hep_job_completes_during_busy_prefix_correspondence.
Goal Logic.True. idtac "AUDIT_END no_early_hep_job_completes_during_busy_prefix_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fca_bool_to_nat_related". exact Logic.I. Qed.
Print Assumptions fca_bool_to_nat_related.
Goal Logic.True. idtac "AUDIT_END fca_bool_to_nat_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fca_sum_filter_related". exact Logic.I. Qed.
Print Assumptions fca_sum_filter_related.
Goal Logic.True. idtac "AUDIT_END fca_sum_filter_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fca_forall_sched". exact Logic.I. Qed.
Print Assumptions fca_forall_sched.
Goal Logic.True. idtac "AUDIT_END fca_forall_sched". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fca_forall_arr". exact Logic.I. Qed.
Print Assumptions fca_forall_arr.
Goal Logic.True. idtac "AUDIT_END fca_forall_arr". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fca_forall_jp". exact Logic.I. Qed.
Print Assumptions fca_forall_jp.
Goal Logic.True. idtac "AUDIT_END fca_forall_jp". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fca_forall_pred". exact Logic.I. Qed.
Print Assumptions fca_forall_pred.
Goal Logic.True. idtac "AUDIT_END fca_forall_pred". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fca_completes_at_related". exact Logic.I. Qed.
Print Assumptions fca_completes_at_related.
Goal Logic.True. idtac "AUDIT_END fca_completes_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fca_completed_dont_execute_rel". exact Logic.I. Qed.
Print Assumptions fca_completed_dont_execute_rel.
Goal Logic.True. idtac "AUDIT_END fca_completed_dont_execute_rel". exact Logic.I. Qed.
