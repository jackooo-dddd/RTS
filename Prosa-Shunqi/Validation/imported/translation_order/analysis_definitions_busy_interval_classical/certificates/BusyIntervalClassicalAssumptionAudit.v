From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence BusyIntervalClassicalCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN quiet_time_correspondence". exact Logic.I. Qed.
Print Assumptions quiet_time_correspondence.
Goal Logic.True. idtac "AUDIT_END quiet_time_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN busy_interval_prefix_correspondence". exact Logic.I. Qed.
Print Assumptions busy_interval_prefix_correspondence.
Goal Logic.True. idtac "AUDIT_END busy_interval_prefix_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN busy_interval_correspondence". exact Logic.I. Qed.
Print Assumptions busy_interval_correspondence.
Goal Logic.True. idtac "AUDIT_END busy_interval_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN quiet_time_dec_correspondence". exact Logic.I. Qed.
Print Assumptions quiet_time_dec_correspondence.
Goal Logic.True. idtac "AUDIT_END quiet_time_dec_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN quiet_time_P_correspondence". exact Logic.I. Qed.
Print Assumptions quiet_time_P_correspondence.
Goal Logic.True. idtac "AUDIT_END quiet_time_P_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bic_lean_transport". exact Logic.I. Qed.
Print Assumptions bic_lean_transport.
Goal Logic.True. idtac "AUDIT_END bic_lean_transport". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bic_nat_input". exact Logic.I. Qed.
Print Assumptions bic_nat_input.
Goal Logic.True. idtac "AUDIT_END bic_nat_input". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bic_false_correspondence". exact Logic.I. Qed.
Print Assumptions bic_false_correspondence.
Goal Logic.True. idtac "AUDIT_END bic_false_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bic_not_correspondence". exact Logic.I. Qed.
Print Assumptions bic_not_correspondence.
Goal Logic.True. idtac "AUDIT_END bic_not_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bic_implb_related". exact Logic.I. Qed.
Print Assumptions bic_implb_related.
Goal Logic.True. idtac "AUDIT_END bic_implb_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bic_all_canonical". exact Logic.I. Qed.
Print Assumptions bic_all_canonical.
Goal Logic.True. idtac "AUDIT_END bic_all_canonical". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bic_all_related". exact Logic.I. Qed.
Print Assumptions bic_all_related.
Goal Logic.True. idtac "AUDIT_END bic_all_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bic_schedule_to_target_rel". exact Logic.I. Qed.
Print Assumptions bic_schedule_to_target_rel.
Goal Logic.True. idtac "AUDIT_END bic_schedule_to_target_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bic_schedule_to_source_rel". exact Logic.I. Qed.
Print Assumptions bic_schedule_to_source_rel.
Goal Logic.True. idtac "AUDIT_END bic_schedule_to_source_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bic_jlfp_to_target_rel". exact Logic.I. Qed.
Print Assumptions bic_jlfp_to_target_rel.
Goal Logic.True. idtac "AUDIT_END bic_jlfp_to_target_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bic_jlfp_to_source_rel". exact Logic.I. Qed.
Print Assumptions bic_jlfp_to_source_rel.
Goal Logic.True. idtac "AUDIT_END bic_jlfp_to_source_rel". exact Logic.I. Qed.
