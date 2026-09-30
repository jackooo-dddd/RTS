From FoundationCertificates Require Import
  EacFullCorrespondence AbCorrespondence ImplTaskCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN concrete_task_source_total". exact Logic.I. Qed.
Print Assumptions concrete_task_source_total.
Goal Logic.True. idtac "AUDIT_END concrete_task_source_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN concrete_task_target_total". exact Logic.I. Qed.
Print Assumptions concrete_task_target_total.
Goal Logic.True. idtac "AUDIT_END concrete_task_target_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN task_eqdef_correspondence". exact Logic.I. Qed.
Print Assumptions task_eqdef_correspondence.
Goal Logic.True. idtac "AUDIT_END task_eqdef_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN eqn_task_correspondence". exact Logic.I. Qed.
Print Assumptions eqn_task_correspondence.
Goal Logic.True. idtac "AUDIT_END eqn_task_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN concrete_job_source_total". exact Logic.I. Qed.
Print Assumptions concrete_job_source_total.
Goal Logic.True. idtac "AUDIT_END concrete_job_source_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN concrete_job_target_total". exact Logic.I. Qed.
Print Assumptions concrete_job_target_total.
Goal Logic.True. idtac "AUDIT_END concrete_job_target_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN get_arrival_curve_prefix_correspondence". exact Logic.I. Qed.
Print Assumptions get_arrival_curve_prefix_correspondence.
Goal Logic.True. idtac "AUDIT_END get_arrival_curve_prefix_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN concrete_max_arrivals_correspondence". exact Logic.I. Qed.
Print Assumptions concrete_max_arrivals_correspondence.
Goal Logic.True. idtac "AUDIT_END concrete_max_arrivals_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_eqdef_correspondence". exact Logic.I. Qed.
Print Assumptions job_eqdef_correspondence.
Goal Logic.True. idtac "AUDIT_END job_eqdef_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN eqn_job_correspondence". exact Logic.I. Qed.
Print Assumptions eqn_job_correspondence.
Goal Logic.True. idtac "AUDIT_END eqn_job_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN TaskCost_correspondence". exact Logic.I. Qed.
Print Assumptions TaskCost_correspondence.
Goal Logic.True. idtac "AUDIT_END TaskCost_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN TaskPriority_correspondence". exact Logic.I. Qed.
Print Assumptions TaskPriority_correspondence.
Goal Logic.True. idtac "AUDIT_END TaskPriority_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN TaskDeadline_correspondence". exact Logic.I. Qed.
Print Assumptions TaskDeadline_correspondence.
Goal Logic.True. idtac "AUDIT_END TaskDeadline_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ConcreteMaxArrivals_correspondence". exact Logic.I. Qed.
Print Assumptions ConcreteMaxArrivals_correspondence.
Goal Logic.True. idtac "AUDIT_END ConcreteMaxArrivals_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN JobTask_correspondence". exact Logic.I. Qed.
Print Assumptions JobTask_correspondence.
Goal Logic.True. idtac "AUDIT_END JobTask_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN JobArrival_correspondence". exact Logic.I. Qed.
Print Assumptions JobArrival_correspondence.
Goal Logic.True. idtac "AUDIT_END JobArrival_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN JobCost_correspondence". exact Logic.I. Qed.
Print Assumptions JobCost_correspondence.
Goal Logic.True. idtac "AUDIT_END JobCost_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN it_task_source_roundtrip". exact Logic.I. Qed.
Print Assumptions it_task_source_roundtrip.
Goal Logic.True. idtac "AUDIT_END it_task_source_roundtrip". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN it_task_target_roundtrip". exact Logic.I. Qed.
Print Assumptions it_task_target_roundtrip.
Goal Logic.True. idtac "AUDIT_END it_task_target_roundtrip". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN it_task_equality". exact Logic.I. Qed.
Print Assumptions it_task_equality.
Goal Logic.True. idtac "AUDIT_END it_task_equality". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN it_task_id". exact Logic.I. Qed.
Print Assumptions it_task_id.
Goal Logic.True. idtac "AUDIT_END it_task_id". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN it_task_cost". exact Logic.I. Qed.
Print Assumptions it_task_cost.
Goal Logic.True. idtac "AUDIT_END it_task_cost". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN it_task_arrival". exact Logic.I. Qed.
Print Assumptions it_task_arrival.
Goal Logic.True. idtac "AUDIT_END it_task_arrival". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN it_task_deadline". exact Logic.I. Qed.
Print Assumptions it_task_deadline.
Goal Logic.True. idtac "AUDIT_END it_task_deadline". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN it_task_priority". exact Logic.I. Qed.
Print Assumptions it_task_priority.
Goal Logic.True. idtac "AUDIT_END it_task_priority". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN it_ab_decide_related". exact Logic.I. Qed.
Print Assumptions it_ab_decide_related.
Goal Logic.True. idtac "AUDIT_END it_ab_decide_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN it_nat_decide_related". exact Logic.I. Qed.
Print Assumptions it_nat_decide_related.
Goal Logic.True. idtac "AUDIT_END it_nat_decide_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN it_task_eqdef_iff". exact Logic.I. Qed.
Print Assumptions it_task_eqdef_iff.
Goal Logic.True. idtac "AUDIT_END it_task_eqdef_iff". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN it_job_source_roundtrip". exact Logic.I. Qed.
Print Assumptions it_job_source_roundtrip.
Goal Logic.True. idtac "AUDIT_END it_job_source_roundtrip". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN it_job_target_roundtrip". exact Logic.I. Qed.
Print Assumptions it_job_target_roundtrip.
Goal Logic.True. idtac "AUDIT_END it_job_target_roundtrip". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN it_job_equality". exact Logic.I. Qed.
Print Assumptions it_job_equality.
Goal Logic.True. idtac "AUDIT_END it_job_equality". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN it_job_id". exact Logic.I. Qed.
Print Assumptions it_job_id.
Goal Logic.True. idtac "AUDIT_END it_job_id". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN it_job_arrival". exact Logic.I. Qed.
Print Assumptions it_job_arrival.
Goal Logic.True. idtac "AUDIT_END it_job_arrival". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN it_job_cost". exact Logic.I. Qed.
Print Assumptions it_job_cost.
Goal Logic.True. idtac "AUDIT_END it_job_cost". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN it_job_deadline". exact Logic.I. Qed.
Print Assumptions it_job_deadline.
Goal Logic.True. idtac "AUDIT_END it_job_deadline". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN it_job_task". exact Logic.I. Qed.
Print Assumptions it_job_task.
Goal Logic.True. idtac "AUDIT_END it_job_task". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN it_task_decide_related". exact Logic.I. Qed.
Print Assumptions it_task_decide_related.
Goal Logic.True. idtac "AUDIT_END it_task_decide_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN it_job_eqdef_iff". exact Logic.I. Qed.
Print Assumptions it_job_eqdef_iff.
Goal Logic.True. idtac "AUDIT_END it_job_eqdef_iff". exact Logic.I. Qed.
