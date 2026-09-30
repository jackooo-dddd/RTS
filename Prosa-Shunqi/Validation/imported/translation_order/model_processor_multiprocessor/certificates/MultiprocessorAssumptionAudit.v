From FoundationCertificates Require Import
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations MultiprocessorCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN processor_source_total". exact Logic.I. Qed.
Print Assumptions processor_source_total.
Goal Logic.True. idtac "AUDIT_END processor_source_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN processor_target_total". exact Logic.I. Qed.
Print Assumptions processor_target_total.
Goal Logic.True. idtac "AUDIT_END processor_target_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN multiprocessor_state_source_total". exact Logic.I. Qed.
Print Assumptions multiprocessor_state_source_total.
Goal Logic.True. idtac "AUDIT_END multiprocessor_state_source_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN multiprocessor_state_target_total". exact Logic.I. Qed.
Print Assumptions multiprocessor_state_target_total.
Goal Logic.True. idtac "AUDIT_END multiprocessor_state_target_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN multiproc_scheduled_on_correspondence". exact Logic.I. Qed.
Print Assumptions multiproc_scheduled_on_correspondence.
Goal Logic.True. idtac "AUDIT_END multiproc_scheduled_on_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN multiproc_supply_on_correspondence". exact Logic.I. Qed.
Print Assumptions multiproc_supply_on_correspondence.
Goal Logic.True. idtac "AUDIT_END multiproc_supply_on_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN multiproc_service_on_correspondence". exact Logic.I. Qed.
Print Assumptions multiproc_service_on_correspondence.
Goal Logic.True. idtac "AUDIT_END multiproc_service_on_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN multiproc_service_in_eq_correspondence". exact Logic.I. Qed.
Print Assumptions multiproc_service_in_eq_correspondence.
Goal Logic.True. idtac "AUDIT_END multiproc_service_in_eq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN mp_nat_lt_correspondence". exact Logic.I. Qed.
Print Assumptions mp_nat_lt_correspondence.
Goal Logic.True. idtac "AUDIT_END mp_nat_lt_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN mp_nat_input". exact Logic.I. Qed.
Print Assumptions mp_nat_input.
Goal Logic.True. idtac "AUDIT_END mp_nat_input". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN mp_ord_rel_canonical". exact Logic.I. Qed.
Print Assumptions mp_ord_rel_canonical.
Goal Logic.True. idtac "AUDIT_END mp_ord_rel_canonical". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN mp_ord_rel_surjective". exact Logic.I. Qed.
Print Assumptions mp_ord_rel_surjective.
Goal Logic.True. idtac "AUDIT_END mp_ord_rel_surjective". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN mp_ord_rel_source_unique". exact Logic.I. Qed.
Print Assumptions mp_ord_rel_source_unique.
Goal Logic.True. idtac "AUDIT_END mp_ord_rel_source_unique". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN mp_ord_rel_target_unique". exact Logic.I. Qed.
Print Assumptions mp_ord_rel_target_unique.
Goal Logic.True. idtac "AUDIT_END mp_ord_rel_target_unique". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN mp_source_ord_sum_as_interval". exact Logic.I. Qed.
Print Assumptions mp_source_ord_sum_as_interval.
Goal Logic.True. idtac "AUDIT_END mp_source_ord_sum_as_interval". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN mp_source_ord_family_lt". exact Logic.I. Qed.
Print Assumptions mp_source_ord_family_lt.
Goal Logic.True. idtac "AUDIT_END mp_source_ord_family_lt". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN mp_source_ord_family_ge". exact Logic.I. Qed.
Print Assumptions mp_source_ord_family_ge.
Goal Logic.True. idtac "AUDIT_END mp_source_ord_family_ge". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN mp_ord_family_related". exact Logic.I. Qed.
Print Assumptions mp_ord_family_related.
Goal Logic.True. idtac "AUDIT_END mp_ord_family_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN mp_fin_sum_related_zero". exact Logic.I. Qed.
Print Assumptions mp_fin_sum_related_zero.
Goal Logic.True. idtac "AUDIT_END mp_fin_sum_related_zero". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN mp_fin_sum_related_one". exact Logic.I. Qed.
Print Assumptions mp_fin_sum_related_one.
Goal Logic.True. idtac "AUDIT_END mp_fin_sum_related_one". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN mp_supply_in_related". exact Logic.I. Qed.
Print Assumptions mp_supply_in_related.
Goal Logic.True. idtac "AUDIT_END mp_supply_in_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN mp_core_sum_related". exact Logic.I. Qed.
Print Assumptions mp_core_sum_related.
Goal Logic.True. idtac "AUDIT_END mp_core_sum_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN mp_multiproc_service_in_related". exact Logic.I. Qed.
Print Assumptions mp_multiproc_service_in_related.
Goal Logic.True. idtac "AUDIT_END mp_multiproc_service_in_related". exact Logic.I. Qed.
