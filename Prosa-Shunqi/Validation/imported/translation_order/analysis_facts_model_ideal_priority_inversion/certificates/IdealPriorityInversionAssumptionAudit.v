From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence PriorityInversionCorrespondence IdealPriorityInversionCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN idle_implies_no_priority_inversion_correspondence". exact Logic.I. Qed.
Print Assumptions idle_implies_no_priority_inversion_correspondence.
Goal Logic.True. idtac "AUDIT_END idle_implies_no_priority_inversion_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN priority_inversion_equiv_sched_lower_priority_correspondence". exact Logic.I. Qed.
Print Assumptions priority_inversion_equiv_sched_lower_priority_correspondence.
Goal Logic.True. idtac "AUDIT_END priority_inversion_equiv_sched_lower_priority_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sched_hep_implies_no_priority_inversion_correspondence". exact Logic.I. Qed.
Print Assumptions sched_hep_implies_no_priority_inversion_correspondence.
Goal Logic.True. idtac "AUDIT_END sched_hep_implies_no_priority_inversion_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sched_lp_implies_priority_inversion_correspondence". exact Logic.I. Qed.
Print Assumptions sched_lp_implies_priority_inversion_correspondence.
Goal Logic.True. idtac "AUDIT_END sched_lp_implies_priority_inversion_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ipi_forall_cover". exact Logic.I. Qed.
Print Assumptions ipi_forall_cover.
Goal Logic.True. idtac "AUDIT_END ipi_forall_cover". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ipi_nat_input". exact Logic.I. Qed.
Print Assumptions ipi_nat_input.
Goal Logic.True. idtac "AUDIT_END ipi_nat_input". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ipi_bool_eq_correspondence". exact Logic.I. Qed.
Print Assumptions ipi_bool_eq_correspondence.
Goal Logic.True. idtac "AUDIT_END ipi_bool_eq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ipi_opt_target_roundtrip". exact Logic.I. Qed.
Print Assumptions ipi_opt_target_roundtrip.
Goal Logic.True. idtac "AUDIT_END ipi_opt_target_roundtrip". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ipi_option_some_eq_correspondence". exact Logic.I. Qed.
Print Assumptions ipi_option_some_eq_correspondence.
Goal Logic.True. idtac "AUDIT_END ipi_option_some_eq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ipi_src_scheduled_on". exact Logic.I. Qed.
Print Assumptions ipi_src_scheduled_on.
Goal Logic.True. idtac "AUDIT_END ipi_src_scheduled_on". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ipi_src_scheduled_in". exact Logic.I. Qed.
Print Assumptions ipi_src_scheduled_in.
Goal Logic.True. idtac "AUDIT_END ipi_src_scheduled_in". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ipi_scheduled_in_related". exact Logic.I. Qed.
Print Assumptions ipi_scheduled_in_related.
Goal Logic.True. idtac "AUDIT_END ipi_scheduled_in_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ipi_sched_to_target_rel". exact Logic.I. Qed.
Print Assumptions ipi_sched_to_target_rel.
Goal Logic.True. idtac "AUDIT_END ipi_sched_to_target_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ipi_sched_to_source_rel". exact Logic.I. Qed.
Print Assumptions ipi_sched_to_source_rel.
Goal Logic.True. idtac "AUDIT_END ipi_sched_to_source_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ipi_forall_sched". exact Logic.I. Qed.
Print Assumptions ipi_forall_sched.
Goal Logic.True. idtac "AUDIT_END ipi_forall_sched". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ipi_jlfp_to_target_rel". exact Logic.I. Qed.
Print Assumptions ipi_jlfp_to_target_rel.
Goal Logic.True. idtac "AUDIT_END ipi_jlfp_to_target_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ipi_jlfp_to_source_rel". exact Logic.I. Qed.
Print Assumptions ipi_jlfp_to_source_rel.
Goal Logic.True. idtac "AUDIT_END ipi_jlfp_to_source_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ipi_forall_jlfp". exact Logic.I. Qed.
Print Assumptions ipi_forall_jlfp.
Goal Logic.True. idtac "AUDIT_END ipi_forall_jlfp". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ipi_reflexive_rel". exact Logic.I. Qed.
Print Assumptions ipi_reflexive_rel.
Goal Logic.True. idtac "AUDIT_END ipi_reflexive_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ipi_scheduled_at_related". exact Logic.I. Qed.
Print Assumptions ipi_scheduled_at_related.
Goal Logic.True. idtac "AUDIT_END ipi_scheduled_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ipi_ideal_is_idle_related". exact Logic.I. Qed.
Print Assumptions ipi_ideal_is_idle_related.
Goal Logic.True. idtac "AUDIT_END ipi_ideal_is_idle_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ipi_jobs_come_from_rel". exact Logic.I. Qed.
Print Assumptions ipi_jobs_come_from_rel.
Goal Logic.True. idtac "AUDIT_END ipi_jobs_come_from_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ipi_jobs_must_arrive_rel". exact Logic.I. Qed.
Print Assumptions ipi_jobs_must_arrive_rel.
Goal Logic.True. idtac "AUDIT_END ipi_jobs_must_arrive_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ipi_scheduled_jobs_at_related". exact Logic.I. Qed.
Print Assumptions ipi_scheduled_jobs_at_related.
Goal Logic.True. idtac "AUDIT_END ipi_scheduled_jobs_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ipi_priority_inversion_related". exact Logic.I. Qed.
Print Assumptions ipi_priority_inversion_related.
Goal Logic.True. idtac "AUDIT_END ipi_priority_inversion_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ipi_prefix_rel". exact Logic.I. Qed.
Print Assumptions ipi_prefix_rel.
Goal Logic.True. idtac "AUDIT_END ipi_prefix_rel". exact Logic.I. Qed.
