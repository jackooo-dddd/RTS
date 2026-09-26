From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations EdfTransCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN earlier_deadline_correspondence". exact Logic.I. Qed.
Print Assumptions earlier_deadline_correspondence.
Goal Logic.True. idtac "AUDIT_END earlier_deadline_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN relevant_pstate_correspondence". exact Logic.I. Qed.
Print Assumptions relevant_pstate_correspondence.
Goal Logic.True. idtac "AUDIT_END relevant_pstate_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN find_swap_candidate_correspondence". exact Logic.I. Qed.
Print Assumptions find_swap_candidate_correspondence.
Goal Logic.True. idtac "AUDIT_END find_swap_candidate_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN make_edf_at_correspondence". exact Logic.I. Qed.
Print Assumptions make_edf_at_correspondence.
Goal Logic.True. idtac "AUDIT_END make_edf_at_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN edf_transform_prefix_correspondence". exact Logic.I. Qed.
Print Assumptions edf_transform_prefix_correspondence.
Goal Logic.True. idtac "AUDIT_END edf_transform_prefix_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN edf_transform_correspondence". exact Logic.I. Qed.
Print Assumptions edf_transform_correspondence.
Goal Logic.True. idtac "AUDIT_END edf_transform_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fet_src_transport". exact Logic.I. Qed.
Print Assumptions fet_src_transport.
Goal Logic.True. idtac "AUDIT_END fet_src_transport". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fet_bool_true". exact Logic.I. Qed.
Print Assumptions fet_bool_true.
Goal Logic.True. idtac "AUDIT_END fet_bool_true". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fet_bool_false". exact Logic.I. Qed.
Print Assumptions fet_bool_false.
Goal Logic.True. idtac "AUDIT_END fet_bool_false". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fet_bool_false_not". exact Logic.I. Qed.
Print Assumptions fet_bool_false_not.
Goal Logic.True. idtac "AUDIT_END fet_bool_false_not". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fet_deadline_of_state_related". exact Logic.I. Qed.
Print Assumptions fet_deadline_of_state_related.
Goal Logic.True. idtac "AUDIT_END fet_deadline_of_state_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fet_src_search_arg_succ". exact Logic.I. Qed.
Print Assumptions fet_src_search_arg_succ.
Goal Logic.True. idtac "AUDIT_END fet_src_search_arg_succ". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fet_search_arg_canonical". exact Logic.I. Qed.
Print Assumptions fet_search_arg_canonical.
Goal Logic.True. idtac "AUDIT_END fet_search_arg_canonical". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fet_find_match_related". exact Logic.I. Qed.
Print Assumptions fet_find_match_related.
Goal Logic.True. idtac "AUDIT_END fet_find_match_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fet_nat_not_eq". exact Logic.I. Qed.
Print Assumptions fet_nat_not_eq.
Goal Logic.True. idtac "AUDIT_END fet_nat_not_eq". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fet_replace_at_related". exact Logic.I. Qed.
Print Assumptions fet_replace_at_related.
Goal Logic.True. idtac "AUDIT_END fet_replace_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fet_swapped_related". exact Logic.I. Qed.
Print Assumptions fet_swapped_related.
Goal Logic.True. idtac "AUDIT_END fet_swapped_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fet_prefix_map_canonical". exact Logic.I. Qed.
Print Assumptions fet_prefix_map_canonical.
Goal Logic.True. idtac "AUDIT_END fet_prefix_map_canonical". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fet_prefix_map_related". exact Logic.I. Qed.
Print Assumptions fet_prefix_map_related.
Goal Logic.True. idtac "AUDIT_END fet_prefix_map_related". exact Logic.I. Qed.
