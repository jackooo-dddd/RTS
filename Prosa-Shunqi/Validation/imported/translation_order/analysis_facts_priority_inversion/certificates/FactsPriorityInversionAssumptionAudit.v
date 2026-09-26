From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence PriorityInversionCorrespondence FactsPriorityInversionCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN sched_itself_implies_no_priority_inversion_correspondence". exact Logic.I. Qed.
Print Assumptions sched_itself_implies_no_priority_inversion_correspondence.
Goal Logic.True. idtac "AUDIT_END sched_itself_implies_no_priority_inversion_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN priority_inversion_scheduled_at_correspondence". exact Logic.I. Qed.
Print Assumptions priority_inversion_scheduled_at_correspondence.
Goal Logic.True. idtac "AUDIT_END priority_inversion_scheduled_at_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN no_priority_inversion_when_idle_correspondence". exact Logic.I. Qed.
Print Assumptions no_priority_inversion_when_idle_correspondence.
Goal Logic.True. idtac "AUDIT_END no_priority_inversion_when_idle_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN priority_inversion_hep_job_correspondence". exact Logic.I. Qed.
Print Assumptions priority_inversion_hep_job_correspondence.
Goal Logic.True. idtac "AUDIT_END priority_inversion_hep_job_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN no_priority_inversion_when_hep_job_scheduled_correspondence". exact Logic.I. Qed.
Print Assumptions no_priority_inversion_when_hep_job_scheduled_correspondence.
Goal Logic.True. idtac "AUDIT_END no_priority_inversion_when_hep_job_scheduled_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN uni_priority_inversion_P_correspondence". exact Logic.I. Qed.
Print Assumptions uni_priority_inversion_P_correspondence.
Goal Logic.True. idtac "AUDIT_END uni_priority_inversion_P_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cumulative_priority_inversion_cat_correspondence". exact Logic.I. Qed.
Print Assumptions cumulative_priority_inversion_cat_correspondence.
Goal Logic.True. idtac "AUDIT_END cumulative_priority_inversion_cat_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fpi_forall_cover_sprop". exact Logic.I. Qed.
Print Assumptions fpi_forall_cover_sprop.
Goal Logic.True. idtac "AUDIT_END fpi_forall_cover_sprop". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fpi_lean_transport". exact Logic.I. Qed.
Print Assumptions fpi_lean_transport.
Goal Logic.True. idtac "AUDIT_END fpi_lean_transport". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fpi_nat_input". exact Logic.I. Qed.
Print Assumptions fpi_nat_input.
Goal Logic.True. idtac "AUDIT_END fpi_nat_input". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fpi_eq_correspondence". exact Logic.I. Qed.
Print Assumptions fpi_eq_correspondence.
Goal Logic.True. idtac "AUDIT_END fpi_eq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fpi_bool_eq_correspondence". exact Logic.I. Qed.
Print Assumptions fpi_bool_eq_correspondence.
Goal Logic.True. idtac "AUDIT_END fpi_bool_eq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fpi_exists_identity". exact Logic.I. Qed.
Print Assumptions fpi_exists_identity.
Goal Logic.True. idtac "AUDIT_END fpi_exists_identity". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fpi_exists2_identity". exact Logic.I. Qed.
Print Assumptions fpi_exists2_identity.
Goal Logic.True. idtac "AUDIT_END fpi_exists2_identity". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fpi_schedule_to_target_rel". exact Logic.I. Qed.
Print Assumptions fpi_schedule_to_target_rel.
Goal Logic.True. idtac "AUDIT_END fpi_schedule_to_target_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fpi_schedule_to_source_rel". exact Logic.I. Qed.
Print Assumptions fpi_schedule_to_source_rel.
Goal Logic.True. idtac "AUDIT_END fpi_schedule_to_source_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fpi_jlfp_to_target_rel". exact Logic.I. Qed.
Print Assumptions fpi_jlfp_to_target_rel.
Goal Logic.True. idtac "AUDIT_END fpi_jlfp_to_target_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fpi_jlfp_to_source_rel". exact Logic.I. Qed.
Print Assumptions fpi_jlfp_to_source_rel.
Goal Logic.True. idtac "AUDIT_END fpi_jlfp_to_source_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fpi_jobs_come_from_related". exact Logic.I. Qed.
Print Assumptions fpi_jobs_come_from_related.
Goal Logic.True. idtac "AUDIT_END fpi_jobs_come_from_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fpi_jobs_must_arrive_related". exact Logic.I. Qed.
Print Assumptions fpi_jobs_must_arrive_related.
Goal Logic.True. idtac "AUDIT_END fpi_jobs_must_arrive_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fpi_reflexive_related". exact Logic.I. Qed.
Print Assumptions fpi_reflexive_related.
Goal Logic.True. idtac "AUDIT_END fpi_reflexive_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fpi_is_idle_related". exact Logic.I. Qed.
Print Assumptions fpi_is_idle_related.
Goal Logic.True. idtac "AUDIT_END fpi_is_idle_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fpi_not_pi_related". exact Logic.I. Qed.
Print Assumptions fpi_not_pi_related.
Goal Logic.True. idtac "AUDIT_END fpi_not_pi_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fpi_uniprocessor_related". exact Logic.I. Qed.
Print Assumptions fpi_uniprocessor_related.
Goal Logic.True. idtac "AUDIT_END fpi_uniprocessor_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fpi_witness_related". exact Logic.I. Qed.
Print Assumptions fpi_witness_related.
Goal Logic.True. idtac "AUDIT_END fpi_witness_related". exact Logic.I. Qed.
