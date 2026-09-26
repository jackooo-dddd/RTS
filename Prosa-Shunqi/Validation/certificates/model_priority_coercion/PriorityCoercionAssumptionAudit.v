From FoundationCertificates Require Import
  PcoBaseAdapter PcoStaticOrder PcoDynamicOrder PriorityCoercionCorrespondence.

Goal Logic.True. idtac "AUDIT_BEGIN FP_to_JLFP_correspondence". exact Logic.I. Qed.
Print Assumptions FP_to_JLFP_correspondence.
Goal Logic.True. idtac "AUDIT_END FP_to_JLFP_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN JLFP_to_JLDP_correspondence". exact Logic.I. Qed.
Print Assumptions JLFP_to_JLDP_correspondence.
Goal Logic.True. idtac "AUDIT_END JLFP_to_JLDP_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN hep_job_at_jlfp_correspondence". exact Logic.I. Qed.
Print Assumptions hep_job_at_jlfp_correspondence.
Goal Logic.True. idtac "AUDIT_END hep_job_at_jlfp_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN hep_job_at_fp_correspondence". exact Logic.I. Qed.
Print Assumptions hep_job_at_fp_correspondence.
Goal Logic.True. idtac "AUDIT_END hep_job_at_fp_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN reflexive_priorities_FP_implies_JLFP_correspondence". exact Logic.I. Qed.
Print Assumptions reflexive_priorities_FP_implies_JLFP_correspondence.
Goal Logic.True. idtac "AUDIT_END reflexive_priorities_FP_implies_JLFP_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN transitive_priorities_FP_implies_JLFP_correspondence". exact Logic.I. Qed.
Print Assumptions transitive_priorities_FP_implies_JLFP_correspondence.
Goal Logic.True. idtac "AUDIT_END transitive_priorities_FP_implies_JLFP_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN total_priorities_FP_implies_JLFP_correspondence". exact Logic.I. Qed.
Print Assumptions total_priorities_FP_implies_JLFP_correspondence.
Goal Logic.True. idtac "AUDIT_END total_priorities_FP_implies_JLFP_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN reflexive_priorities_JLFP_implies_JLDP_correspondence". exact Logic.I. Qed.
Print Assumptions reflexive_priorities_JLFP_implies_JLDP_correspondence.
Goal Logic.True. idtac "AUDIT_END reflexive_priorities_JLFP_implies_JLDP_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN transitive_priorities_JLFP_implies_JLDP_correspondence". exact Logic.I. Qed.
Print Assumptions transitive_priorities_JLFP_implies_JLDP_correspondence.
Goal Logic.True. idtac "AUDIT_END transitive_priorities_JLFP_implies_JLDP_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN total_priorities_JLFP_implies_JLDP_correspondence". exact Logic.I. Qed.
Print Assumptions total_priorities_JLFP_implies_JLDP_correspondence.
Goal Logic.True. idtac "AUDIT_END total_priorities_JLFP_implies_JLDP_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pco_forall_fp". exact Logic.I. Qed.
Print Assumptions pco_forall_fp.
Goal Logic.True. idtac "AUDIT_END pco_forall_fp". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pco_forall_jlfp". exact Logic.I. Qed.
Print Assumptions pco_forall_jlfp.
Goal Logic.True. idtac "AUDIT_END pco_forall_jlfp". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pco_forall_nat". exact Logic.I. Qed.
Print Assumptions pco_forall_nat.
Goal Logic.True. idtac "AUDIT_END pco_forall_nat". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pco_hep_task_of_jobs". exact Logic.I. Qed.
Print Assumptions pco_hep_task_of_jobs.
Goal Logic.True. idtac "AUDIT_END pco_hep_task_of_jobs". exact Logic.I. Qed.
