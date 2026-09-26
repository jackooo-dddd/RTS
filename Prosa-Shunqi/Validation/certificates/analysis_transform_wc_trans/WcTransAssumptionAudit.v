From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence WcTransCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN relevant_pstate_correspondence". exact Logic.I. Qed.
Print Assumptions relevant_pstate_correspondence.
Goal Logic.True. idtac "AUDIT_END relevant_pstate_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN max_deadline_for_jobs_arrived_before_correspondence". exact Logic.I. Qed.
Print Assumptions max_deadline_for_jobs_arrived_before_correspondence.
Goal Logic.True. idtac "AUDIT_END max_deadline_for_jobs_arrived_before_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN find_swap_candidate_correspondence". exact Logic.I. Qed.
Print Assumptions find_swap_candidate_correspondence.
Goal Logic.True. idtac "AUDIT_END find_swap_candidate_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN make_wc_at_correspondence". exact Logic.I. Qed.
Print Assumptions make_wc_at_correspondence.
Goal Logic.True. idtac "AUDIT_END make_wc_at_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wc_transform_prefix_correspondence". exact Logic.I. Qed.
Print Assumptions wc_transform_prefix_correspondence.
Goal Logic.True. idtac "AUDIT_END wc_transform_prefix_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wc_transform_correspondence". exact Logic.I. Qed.
Print Assumptions wc_transform_correspondence.
Goal Logic.True. idtac "AUDIT_END wc_transform_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wct_map_deadline_canonical". exact Logic.I. Qed.
Print Assumptions wct_map_deadline_canonical.
Goal Logic.True. idtac "AUDIT_END wct_map_deadline_canonical". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wct_src_search_arg_succ". exact Logic.I. Qed.
Print Assumptions wct_src_search_arg_succ.
Goal Logic.True. idtac "AUDIT_END wct_src_search_arg_succ". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wct_search_arg_canonical". exact Logic.I. Qed.
Print Assumptions wct_search_arg_canonical.
Goal Logic.True. idtac "AUDIT_END wct_search_arg_canonical". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wct_find_match_related". exact Logic.I. Qed.
Print Assumptions wct_find_match_related.
Goal Logic.True. idtac "AUDIT_END wct_find_match_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wct_nat_not_eq". exact Logic.I. Qed.
Print Assumptions wct_nat_not_eq.
Goal Logic.True. idtac "AUDIT_END wct_nat_not_eq". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wct_replace_at_related". exact Logic.I. Qed.
Print Assumptions wct_replace_at_related.
Goal Logic.True. idtac "AUDIT_END wct_replace_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wct_swapped_related". exact Logic.I. Qed.
Print Assumptions wct_swapped_related.
Goal Logic.True. idtac "AUDIT_END wct_swapped_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wct_prefix_map_canonical". exact Logic.I. Qed.
Print Assumptions wct_prefix_map_canonical.
Goal Logic.True. idtac "AUDIT_END wct_prefix_map_canonical". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN wct_prefix_map_related". exact Logic.I. Qed.
Print Assumptions wct_prefix_map_related.
Goal Logic.True. idtac "AUDIT_END wct_prefix_map_related". exact Logic.I. Qed.
