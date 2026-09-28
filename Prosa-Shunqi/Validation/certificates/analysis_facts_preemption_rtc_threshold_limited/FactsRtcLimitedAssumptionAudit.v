From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence LimitedPreemptiveCorrespondence ScheduleLimitedPreemptiveCorrespondence TaskPreemptionParametersCorrespondence TaskLimitedPreemptiveCorrespondence FactsRtcLimitedCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN number_of_preemption_points_in_task_at_least_two_correspondence". exact Logic.I. Qed.
Print Assumptions number_of_preemption_points_in_task_at_least_two_correspondence.
Goal Logic.True. idtac "AUDIT_END number_of_preemption_points_in_task_at_least_two_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN limited_valid_task_run_to_completion_threshold_correspondence". exact Logic.I. Qed.
Print Assumptions limited_valid_task_run_to_completion_threshold_correspondence.
Goal Logic.True. idtac "AUDIT_END limited_valid_task_run_to_completion_threshold_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN last_segment_eq_cost_minus_rtct_correspondence". exact Logic.I. Qed.
Print Assumptions last_segment_eq_cost_minus_rtct_correspondence.
Goal Logic.True. idtac "AUDIT_END last_segment_eq_cost_minus_rtct_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN frl_forall_list". exact Logic.I. Qed.
Print Assumptions frl_forall_list.
Goal Logic.True. idtac "AUDIT_END frl_forall_list". exact Logic.I. Qed.
