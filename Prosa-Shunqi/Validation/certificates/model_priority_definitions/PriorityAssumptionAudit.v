From PriorityCertificates Require Import PriorityBaseAdapter PriorityStaticOrder
  PriorityDynamicOrder PriorityPolicyProperties PriorityDerived
  PriorityListAdapter PriorityAntisymmetric.

Goal Logic.True. Proof. idtac "AUDIT_BEGIN pd_fp_import_certificate". exact I. Qed.
Print Assumptions pd_fp_import_certificate.
Goal Logic.True. Proof. idtac "AUDIT_END pd_fp_import_certificate". exact I. Qed.

Goal Logic.True. Proof. idtac "AUDIT_BEGIN pd_fp_export_certificate". exact I. Qed.
Print Assumptions pd_fp_export_certificate.
Goal Logic.True. Proof. idtac "AUDIT_END pd_fp_export_certificate". exact I. Qed.

Goal Logic.True. Proof. idtac "AUDIT_BEGIN pd_jlfp_import_certificate". exact I. Qed.
Print Assumptions pd_jlfp_import_certificate.
Goal Logic.True. Proof. idtac "AUDIT_END pd_jlfp_import_certificate". exact I. Qed.

Goal Logic.True. Proof. idtac "AUDIT_BEGIN pd_jlfp_export_certificate". exact I. Qed.
Print Assumptions pd_jlfp_export_certificate.
Goal Logic.True. Proof. idtac "AUDIT_END pd_jlfp_export_certificate". exact I. Qed.

Goal Logic.True. Proof. idtac "AUDIT_BEGIN pd_jldp_import_certificate". exact I. Qed.
Print Assumptions pd_jldp_import_certificate.
Goal Logic.True. Proof. idtac "AUDIT_END pd_jldp_import_certificate". exact I. Qed.

Goal Logic.True. Proof. idtac "AUDIT_BEGIN pd_jldp_export_certificate". exact I. Qed.
Print Assumptions pd_jldp_export_certificate.
Goal Logic.True. Proof. idtac "AUDIT_END pd_jldp_export_certificate". exact I. Qed.

Goal Logic.True. Proof. idtac "AUDIT_BEGIN pd_reflexive_priorities_certificate". exact I. Qed.
Print Assumptions pd_reflexive_priorities_certificate.
Goal Logic.True. Proof. idtac "AUDIT_END pd_reflexive_priorities_certificate". exact I. Qed.

Goal Logic.True. Proof. idtac "AUDIT_BEGIN pd_transitive_priorities_certificate". exact I. Qed.
Print Assumptions pd_transitive_priorities_certificate.
Goal Logic.True. Proof. idtac "AUDIT_END pd_transitive_priorities_certificate". exact I. Qed.

Goal Logic.True. Proof. idtac "AUDIT_BEGIN pd_total_priorities_certificate". exact I. Qed.
Print Assumptions pd_total_priorities_certificate.
Goal Logic.True. Proof. idtac "AUDIT_END pd_total_priorities_certificate". exact I. Qed.

Goal Logic.True. Proof. idtac "AUDIT_BEGIN pd_reflexive_job_priorities_certificate". exact I. Qed.
Print Assumptions pd_reflexive_job_priorities_certificate.
Goal Logic.True. Proof. idtac "AUDIT_END pd_reflexive_job_priorities_certificate". exact I. Qed.

Goal Logic.True. Proof. idtac "AUDIT_BEGIN pd_transitive_job_priorities_certificate". exact I. Qed.
Print Assumptions pd_transitive_job_priorities_certificate.
Goal Logic.True. Proof. idtac "AUDIT_END pd_transitive_job_priorities_certificate". exact I. Qed.

Goal Logic.True. Proof. idtac "AUDIT_BEGIN pd_total_job_priorities_certificate". exact I. Qed.
Print Assumptions pd_total_job_priorities_certificate.
Goal Logic.True. Proof. idtac "AUDIT_END pd_total_job_priorities_certificate". exact I. Qed.

Goal Logic.True. Proof. idtac "AUDIT_BEGIN pd_policy_respects_sequential_tasks_certificate". exact I. Qed.
Print Assumptions pd_policy_respects_sequential_tasks_certificate.
Goal Logic.True. Proof. idtac "AUDIT_END pd_policy_respects_sequential_tasks_certificate". exact I. Qed.

Goal Logic.True. Proof. idtac "AUDIT_BEGIN pd_policy_is_FIFO_certificate". exact I. Qed.
Print Assumptions pd_policy_is_FIFO_certificate.
Goal Logic.True. Proof. idtac "AUDIT_END pd_policy_is_FIFO_certificate". exact I. Qed.

Goal Logic.True. Proof. idtac "AUDIT_BEGIN pd_reflexive_task_priorities_certificate". exact I. Qed.
Print Assumptions pd_reflexive_task_priorities_certificate.
Goal Logic.True. Proof. idtac "AUDIT_END pd_reflexive_task_priorities_certificate". exact I. Qed.

Goal Logic.True. Proof. idtac "AUDIT_BEGIN pd_transitive_task_priorities_certificate". exact I. Qed.
Print Assumptions pd_transitive_task_priorities_certificate.
Goal Logic.True. Proof. idtac "AUDIT_END pd_transitive_task_priorities_certificate". exact I. Qed.

Goal Logic.True. Proof. idtac "AUDIT_BEGIN pd_total_task_priorities_certificate". exact I. Qed.
Print Assumptions pd_total_task_priorities_certificate.
Goal Logic.True. Proof. idtac "AUDIT_END pd_total_task_priorities_certificate". exact I. Qed.

Goal Logic.True. Proof. idtac "AUDIT_BEGIN pd_antisymmetric_over_taskset_certificate". exact I. Qed.
Print Assumptions pd_antisymmetric_over_taskset_certificate.
Goal Logic.True. Proof. idtac "AUDIT_END pd_antisymmetric_over_taskset_certificate". exact I. Qed.

Goal Logic.True. Proof. idtac "AUDIT_BEGIN pd_another_hep_job_certificate". exact I. Qed.
Print Assumptions pd_another_hep_job_certificate.
Goal Logic.True. Proof. idtac "AUDIT_END pd_another_hep_job_certificate". exact I. Qed.

Goal Logic.True. Proof. idtac "AUDIT_BEGIN pd_another_task_hep_job_certificate". exact I. Qed.
Print Assumptions pd_another_task_hep_job_certificate.
Goal Logic.True. Proof. idtac "AUDIT_END pd_another_task_hep_job_certificate". exact I. Qed.

Goal Logic.True. Proof. idtac "AUDIT_BEGIN pd_another_hep_job_of_same_task_certificate". exact I. Qed.
Print Assumptions pd_another_hep_job_of_same_task_certificate.
Goal Logic.True. Proof. idtac "AUDIT_END pd_another_hep_job_of_same_task_certificate". exact I. Qed.

Goal Logic.True. Proof. idtac "AUDIT_BEGIN pd_hp_task_certificate". exact I. Qed.
Print Assumptions pd_hp_task_certificate.
Goal Logic.True. Proof. idtac "AUDIT_END pd_hp_task_certificate". exact I. Qed.

Goal Logic.True. Proof. idtac "AUDIT_BEGIN pd_ep_task_certificate". exact I. Qed.
Print Assumptions pd_ep_task_certificate.
Goal Logic.True. Proof. idtac "AUDIT_END pd_ep_task_certificate". exact I. Qed.
