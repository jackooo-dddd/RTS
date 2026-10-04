From FoundationCertificates Require Import ClassicUniPlatformTdmaCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN Platform_TDMA_sched_implies_in_slot_correspondence". exact Logic.I. Qed.
Print Assumptions Platform_TDMA_sched_implies_in_slot_correspondence.
Goal Logic.True. idtac "AUDIT_END Platform_TDMA_sched_implies_in_slot_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Platform_TDMA_backlogged_implies_not_in_slot_or_other_job_sched_correspondence". exact Logic.I. Qed.
Print Assumptions Platform_TDMA_backlogged_implies_not_in_slot_or_other_job_sched_correspondence.
Goal Logic.True. idtac "AUDIT_END Platform_TDMA_backlogged_implies_not_in_slot_or_other_job_sched_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Platform_TDMA_Respects_TDMA_policy_correspondence". exact Logic.I. Qed.
Print Assumptions Platform_TDMA_Respects_TDMA_policy_correspondence.
Goal Logic.True. idtac "AUDIT_END Platform_TDMA_Respects_TDMA_policy_correspondence". exact Logic.I. Qed.
