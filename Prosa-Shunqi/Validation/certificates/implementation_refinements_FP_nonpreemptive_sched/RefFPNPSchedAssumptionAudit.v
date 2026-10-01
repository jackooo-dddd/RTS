From FoundationCertificates Require Import
  PsEac PsAb PsImplTask PsListOps PsSvcBase PsSvcNatBool PsSvcInterval PsSched RefFPNPSchedCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN Task_source_total". exact Logic.I. Qed.
Print Assumptions Task_source_total.
Goal Logic.True. idtac "AUDIT_END Task_source_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Task_target_total". exact Logic.I. Qed.
Print Assumptions Task_target_total.
Goal Logic.True. idtac "AUDIT_END Task_target_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Job_source_total". exact Logic.I. Qed.
Print Assumptions Job_source_total.
Goal Logic.True. idtac "AUDIT_END Job_source_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Job_target_total". exact Logic.I. Qed.
Print Assumptions Job_target_total.
Goal Logic.True. idtac "AUDIT_END Job_target_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sequential_ready_instance_correspondence". exact Logic.I. Qed.
Print Assumptions sequential_ready_instance_correspondence.
Goal Logic.True. idtac "AUDIT_END sequential_ready_instance_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sched_correspondence". exact Logic.I. Qed.
Print Assumptions sched_correspondence.
Goal Logic.True. idtac "AUDIT_END sched_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sched_jobs_must_be_ready_to_execute_correspondence". exact Logic.I. Qed.
Print Assumptions sched_jobs_must_be_ready_to_execute_correspondence.
Goal Logic.True. idtac "AUDIT_END sched_jobs_must_be_ready_to_execute_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sched_valid_correspondence". exact Logic.I. Qed.
Print Assumptions sched_valid_correspondence.
Goal Logic.True. idtac "AUDIT_END sched_valid_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sched_nonpreemptive_next_correspondence". exact Logic.I. Qed.
Print Assumptions sched_nonpreemptive_next_correspondence.
Goal Logic.True. idtac "AUDIT_END sched_nonpreemptive_next_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sched_nonpreemptive_correspondence". exact Logic.I. Qed.
Print Assumptions sched_nonpreemptive_correspondence.
Goal Logic.True. idtac "AUDIT_END sched_nonpreemptive_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN respects_policy_at_preemption_point_np_correspondence". exact Logic.I. Qed.
Print Assumptions respects_policy_at_preemption_point_np_correspondence.
Goal Logic.True. idtac "AUDIT_END respects_policy_at_preemption_point_np_correspondence". exact Logic.I. Qed.
