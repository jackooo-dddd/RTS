From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations FactsReplaceAtCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN replace_at_def_correspondence". exact Logic.I. Qed.
Print Assumptions replace_at_def_correspondence.
Goal Logic.True. idtac "AUDIT_END replace_at_def_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rest_of_schedule_invariant_correspondence". exact Logic.I. Qed.
Print Assumptions rest_of_schedule_invariant_correspondence.
Goal Logic.True. idtac "AUDIT_END rest_of_schedule_invariant_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_at_other_times_invariant_correspondence". exact Logic.I. Qed.
Print Assumptions service_at_other_times_invariant_correspondence.
Goal Logic.True. idtac "AUDIT_END service_at_other_times_invariant_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_delta_correspondence". exact Logic.I. Qed.
Print Assumptions service_delta_correspondence.
Goal Logic.True. idtac "AUDIT_END service_delta_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_in_replaced_correspondence". exact Logic.I. Qed.
Print Assumptions service_in_replaced_correspondence.
Goal Logic.True. idtac "AUDIT_END service_in_replaced_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_at_of_others_invariant_correspondence". exact Logic.I. Qed.
Print Assumptions service_at_of_others_invariant_correspondence.
Goal Logic.True. idtac "AUDIT_END service_at_of_others_invariant_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_during_of_others_invariant_correspondence". exact Logic.I. Qed.
Print Assumptions service_during_of_others_invariant_correspondence.
Goal Logic.True. idtac "AUDIT_END service_during_of_others_invariant_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fra_nat_input". exact Logic.I. Qed.
Print Assumptions fra_nat_input.
Goal Logic.True. idtac "AUDIT_END fra_nat_input". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fra_false_correspondence". exact Logic.I. Qed.
Print Assumptions fra_false_correspondence.
Goal Logic.True. idtac "AUDIT_END fra_false_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fra_nat_neq_correspondence". exact Logic.I. Qed.
Print Assumptions fra_nat_neq_correspondence.
Goal Logic.True. idtac "AUDIT_END fra_nat_neq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fra_or_correspondence". exact Logic.I. Qed.
Print Assumptions fra_or_correspondence.
Goal Logic.True. idtac "AUDIT_END fra_or_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fra_lean_transport". exact Logic.I. Qed.
Print Assumptions fra_lean_transport.
Goal Logic.True. idtac "AUDIT_END fra_lean_transport". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fra_state_rel". exact Logic.I. Qed.
Print Assumptions fra_state_rel.
Goal Logic.True. idtac "AUDIT_END fra_state_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fra_state_eq_correspondence". exact Logic.I. Qed.
Print Assumptions fra_state_eq_correspondence.
Goal Logic.True. idtac "AUDIT_END fra_state_eq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fra_nat_not_eq". exact Logic.I. Qed.
Print Assumptions fra_nat_not_eq.
Goal Logic.True. idtac "AUDIT_END fra_nat_not_eq". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fra_src_same". exact Logic.I. Qed.
Print Assumptions fra_src_same.
Goal Logic.True. idtac "AUDIT_END fra_src_same". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fra_src_other". exact Logic.I. Qed.
Print Assumptions fra_src_other.
Goal Logic.True. idtac "AUDIT_END fra_src_other". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fra_replace_at_fun". exact Logic.I. Qed.
Print Assumptions fra_replace_at_fun.
Goal Logic.True. idtac "AUDIT_END fra_replace_at_fun". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fra_service_at_related". exact Logic.I. Qed.
Print Assumptions fra_service_at_related.
Goal Logic.True. idtac "AUDIT_END fra_service_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fra_service_during_related". exact Logic.I. Qed.
Print Assumptions fra_service_during_related.
Goal Logic.True. idtac "AUDIT_END fra_service_during_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fra_not_scheduled_related". exact Logic.I. Qed.
Print Assumptions fra_not_scheduled_related.
Goal Logic.True. idtac "AUDIT_END fra_not_scheduled_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fra_window_related". exact Logic.I. Qed.
Print Assumptions fra_window_related.
Goal Logic.True. idtac "AUDIT_END fra_window_related". exact Logic.I. Qed.
