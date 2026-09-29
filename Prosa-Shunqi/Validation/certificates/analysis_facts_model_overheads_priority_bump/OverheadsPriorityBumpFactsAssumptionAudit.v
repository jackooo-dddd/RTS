From FoundationCertificates Require Import
  OvhArrivalsSeqBaseAdapter OvhArrivalsSeqOperations OvhArrivalsSeqCorrespondence OvhArrivalsCorrespondence OvhJitterSvcBaseAdapter OvhJitterSvcNatBoolOperations OvhJitterSvcIntervalOperations OvhJitterSvcScheduleOperations OvhJitterSvcJobOperations OvhPreemptionParameterCorrespondence OvhPreemptionTimeCorrespondence OvhPriorityDrivenCorrespondence OvhPStateCoverHelpers OvhFactsPreemptionHelpers OvhWorkloadCorrespondence OvhPriorityInversionCorrespondence OvhExistenceHelpers OvhHepAtPtHelpers OvhTaskPreemptionParametersCorrespondence OvhBusyIntervalPiHelpers OvhStateRel PriorityBumpCorrespondence OverheadsPriorityBumpFactsCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN priority_bump_implies_preemption_time_correspondence". exact Logic.I. Qed.
Print Assumptions priority_bump_implies_preemption_time_correspondence.
Goal Logic.True. idtac "AUDIT_END priority_bump_implies_preemption_time_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN priority_bump_implies_hp_arrival_in_prefix_correspondence". exact Logic.I. Qed.
Print Assumptions priority_bump_implies_hp_arrival_in_prefix_correspondence.
Goal Logic.True. idtac "AUDIT_END priority_bump_implies_hp_arrival_in_prefix_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN no_priority_bumps_in_fifo_correspondence". exact Logic.I. Qed.
Print Assumptions no_priority_bumps_in_fifo_correspondence.
Goal Logic.True. idtac "AUDIT_END no_priority_bumps_in_fifo_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pbf_pb_ar". exact Logic.I. Qed.
Print Assumptions pbf_pb_ar.
Goal Logic.True. idtac "AUDIT_END pbf_pb_ar". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pbf_ar_pb". exact Logic.I. Qed.
Print Assumptions pbf_ar_pb.
Goal Logic.True. idtac "AUDIT_END pbf_ar_pb". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pbf_sched_rel". exact Logic.I. Qed.
Print Assumptions pbf_sched_rel.
Goal Logic.True. idtac "AUDIT_END pbf_sched_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pbf_jlfp_rel". exact Logic.I. Qed.
Print Assumptions pbf_jlfp_rel.
Goal Logic.True. idtac "AUDIT_END pbf_jlfp_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pbf_bump_related". exact Logic.I. Qed.
Print Assumptions pbf_bump_related.
Goal Logic.True. idtac "AUDIT_END pbf_bump_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pbf_not_bump_related". exact Logic.I. Qed.
Print Assumptions pbf_not_bump_related.
Goal Logic.True. idtac "AUDIT_END pbf_not_bump_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pbf_forall_ja". exact Logic.I. Qed.
Print Assumptions pbf_forall_ja.
Goal Logic.True. idtac "AUDIT_END pbf_forall_ja". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pbf_forall_cost". exact Logic.I. Qed.
Print Assumptions pbf_forall_cost.
Goal Logic.True. idtac "AUDIT_END pbf_forall_cost". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pbf_basic_ready_rel". exact Logic.I. Qed.
Print Assumptions pbf_basic_ready_rel.
Goal Logic.True. idtac "AUDIT_END pbf_basic_ready_rel". exact Logic.I. Qed.
