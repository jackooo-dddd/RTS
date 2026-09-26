From FoundationCertificates Require Import
  TdmaBaseAdapter TdmaArithmeticAdapter TdmaSeqsetAdapter TdmaPolicyAdapter
  TdmaValidityCorrespondence TdmaNumericCorrespondence TdmaJobTaskAdapter
  TdmaProcessorOperations TdmaArrivalOperations TdmaScheduleCorrespondence.

Goal Logic.True. idtac "AUDIT_BEGIN TDMA_slot_source_total". exact Logic.I. Qed.
Print Assumptions TDMA_slot_source_total.
Goal Logic.True. idtac "AUDIT_END TDMA_slot_source_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN TDMA_slot_target_total". exact Logic.I. Qed.
Print Assumptions TDMA_slot_target_total.
Goal Logic.True. idtac "AUDIT_END TDMA_slot_target_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN TDMA_slot_order_source_total". exact Logic.I. Qed.
Print Assumptions TDMA_slot_order_source_total.
Goal Logic.True. idtac "AUDIT_END TDMA_slot_order_source_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN TDMA_slot_order_target_total". exact Logic.I. Qed.
Print Assumptions TDMA_slot_order_target_total.
Goal Logic.True. idtac "AUDIT_END TDMA_slot_order_target_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN tdma_policy_source_total". exact Logic.I. Qed.
Print Assumptions tdma_policy_source_total.
Goal Logic.True. idtac "AUDIT_END tdma_policy_source_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN tdma_policy_target_total". exact Logic.I. Qed.
Print Assumptions tdma_policy_target_total.
Goal Logic.True. idtac "AUDIT_END tdma_policy_target_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN transitive_slot_order_correspondence". exact Logic.I. Qed.
Print Assumptions transitive_slot_order_correspondence.
Goal Logic.True. idtac "AUDIT_END transitive_slot_order_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN total_slot_order_correspondence". exact Logic.I. Qed.
Print Assumptions total_slot_order_correspondence.
Goal Logic.True. idtac "AUDIT_END total_slot_order_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN antisymmetric_slot_order_correspondence". exact Logic.I. Qed.
Print Assumptions antisymmetric_slot_order_correspondence.
Goal Logic.True. idtac "AUDIT_END antisymmetric_slot_order_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN valid_time_slot_correspondence". exact Logic.I. Qed.
Print Assumptions valid_time_slot_correspondence.
Goal Logic.True. idtac "AUDIT_END valid_time_slot_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN valid_TDMAPolicy_correspondence". exact Logic.I. Qed.
Print Assumptions valid_TDMAPolicy_correspondence.
Goal Logic.True. idtac "AUDIT_END valid_TDMAPolicy_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN TDMA_cycle_correspondence". exact Logic.I. Qed.
Print Assumptions TDMA_cycle_correspondence.
Goal Logic.True. idtac "AUDIT_END TDMA_cycle_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN task_slot_offset_correspondence". exact Logic.I. Qed.
Print Assumptions task_slot_offset_correspondence.
Goal Logic.True. idtac "AUDIT_END task_slot_offset_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN task_in_time_slot_correspondence". exact Logic.I. Qed.
Print Assumptions task_in_time_slot_correspondence.
Goal Logic.True. idtac "AUDIT_END task_in_time_slot_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_in_time_slot_correspondence". exact Logic.I. Qed.
Print Assumptions job_in_time_slot_correspondence.
Goal Logic.True. idtac "AUDIT_END job_in_time_slot_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sched_implies_in_slot_correspondence". exact Logic.I. Qed.
Print Assumptions sched_implies_in_slot_correspondence.
Goal Logic.True. idtac "AUDIT_END sched_implies_in_slot_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN backlogged_implies_not_in_slot_or_other_job_sched_correspondence". exact Logic.I. Qed.
Print Assumptions backlogged_implies_not_in_slot_or_other_job_sched_correspondence.
Goal Logic.True. idtac "AUDIT_END backlogged_implies_not_in_slot_or_other_job_sched_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN respects_TDMA_policy_correspondence". exact Logic.I. Qed.
Print Assumptions respects_TDMA_policy_correspondence.
Goal Logic.True. idtac "AUDIT_END respects_TDMA_policy_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN seqset_relation_source_total". exact Logic.I. Qed.
Print Assumptions seqset_relation_source_total.
Goal Logic.True. idtac "AUDIT_END seqset_relation_source_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN tdma_job_task_source_total". exact Logic.I. Qed.
Print Assumptions tdma_job_task_source_total.
Goal Logic.True. idtac "AUDIT_END tdma_job_task_source_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN tdma_job_arrival_source_total". exact Logic.I. Qed.
Print Assumptions tdma_job_arrival_source_total.
Goal Logic.True. idtac "AUDIT_END tdma_job_arrival_source_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN edf_schedule_canonical". exact Logic.I. Qed.
Print Assumptions edf_schedule_canonical.
Goal Logic.True. idtac "AUDIT_END edf_schedule_canonical". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN tdma_arrival_sequence_source_total". exact Logic.I. Qed.
Print Assumptions tdma_arrival_sequence_source_total.
Goal Logic.True. idtac "AUDIT_END tdma_arrival_sequence_source_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN tdma_arrives_in_related". exact Logic.I. Qed.
Print Assumptions tdma_arrives_in_related.
Goal Logic.True. idtac "AUDIT_END tdma_arrives_in_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN tdma_nat_sub_related". exact Logic.I. Qed.
Print Assumptions tdma_nat_sub_related.
Goal Logic.True. idtac "AUDIT_END tdma_nat_sub_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN tdma_nat_mod_related". exact Logic.I. Qed.
Print Assumptions tdma_nat_mod_related.
Goal Logic.True. idtac "AUDIT_END tdma_nat_mod_related". exact Logic.I. Qed.
