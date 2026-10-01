From FoundationCertificates Require Import
  RtBase RtArrivalBound RefTaskCorrespondence.
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

Goal Logic.True. idtac "AUDIT_BEGIN task_T_source_total". exact Logic.I. Qed.
Print Assumptions task_T_source_total.
Goal Logic.True. idtac "AUDIT_END task_T_source_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN task_T_target_total". exact Logic.I. Qed.
Print Assumptions task_T_target_total.
Goal Logic.True. idtac "AUDIT_END task_T_target_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN task_eqdef_T_correspondence". exact Logic.I. Qed.
Print Assumptions task_eqdef_T_correspondence.
Goal Logic.True. idtac "AUDIT_END task_eqdef_T_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN inter_arrival_to_extrapolated_arrival_curve_T_correspondence". exact Logic.I. Qed.
Print Assumptions inter_arrival_to_extrapolated_arrival_curve_T_correspondence.
Goal Logic.True. idtac "AUDIT_END inter_arrival_to_extrapolated_arrival_curve_T_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN get_extrapolated_arrival_curve_T_correspondence". exact Logic.I. Qed.
Print Assumptions get_extrapolated_arrival_curve_T_correspondence.
Goal Logic.True. idtac "AUDIT_END get_extrapolated_arrival_curve_T_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ConcreteMaxArrivals_T_correspondence". exact Logic.I. Qed.
Print Assumptions ConcreteMaxArrivals_T_correspondence.
Goal Logic.True. idtac "AUDIT_END ConcreteMaxArrivals_T_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN task_rbf_T_correspondence". exact Logic.I. Qed.
Print Assumptions task_rbf_T_correspondence.
Goal Logic.True. idtac "AUDIT_END task_rbf_T_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN valid_arrivals_T_correspondence". exact Logic.I. Qed.
Print Assumptions valid_arrivals_T_correspondence.
Goal Logic.True. idtac "AUDIT_END valid_arrivals_T_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN get_horizon_of_task_T_correspondence". exact Logic.I. Qed.
Print Assumptions get_horizon_of_task_T_correspondence.
Goal Logic.True. idtac "AUDIT_END get_horizon_of_task_T_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN get_time_steps_of_task_T_correspondence". exact Logic.I. Qed.
Print Assumptions get_time_steps_of_task_T_correspondence.
Goal Logic.True. idtac "AUDIT_END get_time_steps_of_task_T_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN time_steps_with_offset_T_correspondence". exact Logic.I. Qed.
Print Assumptions time_steps_with_offset_T_correspondence.
Goal Logic.True. idtac "AUDIT_END time_steps_with_offset_T_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN repeat_steps_with_offset_T_correspondence". exact Logic.I. Qed.
Print Assumptions repeat_steps_with_offset_T_correspondence.
Goal Logic.True. idtac "AUDIT_END repeat_steps_with_offset_T_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN taskT_to_task_correspondence". exact Logic.I. Qed.
Print Assumptions taskT_to_task_correspondence.
Goal Logic.True. idtac "AUDIT_END taskT_to_task_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Rtask_correspondence". exact Logic.I. Qed.
Print Assumptions Rtask_correspondence.
Goal Logic.True. idtac "AUDIT_END Rtask_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN task_to_taskT_correspondence". exact Logic.I. Qed.
Print Assumptions task_to_taskT_correspondence.
Goal Logic.True. idtac "AUDIT_END task_to_taskT_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN refine_task_correspondence". exact Logic.I. Qed.
Print Assumptions refine_task_correspondence.
Goal Logic.True. idtac "AUDIT_END refine_task_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN refine_task_id_correspondence". exact Logic.I. Qed.
Print Assumptions refine_task_id_correspondence.
Goal Logic.True. idtac "AUDIT_END refine_task_id_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN refine_task_cost_correspondence". exact Logic.I. Qed.
Print Assumptions refine_task_cost_correspondence.
Goal Logic.True. idtac "AUDIT_END refine_task_cost_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN refine_task_arrival_correspondence". exact Logic.I. Qed.
Print Assumptions refine_task_arrival_correspondence.
Goal Logic.True. idtac "AUDIT_END refine_task_arrival_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN refine_task_deadline_correspondence". exact Logic.I. Qed.
Print Assumptions refine_task_deadline_correspondence.
Goal Logic.True. idtac "AUDIT_END refine_task_deadline_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN refine_task_priority_correspondence". exact Logic.I. Qed.
Print Assumptions refine_task_priority_correspondence.
Goal Logic.True. idtac "AUDIT_END refine_task_priority_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN refine_Periodic_correspondence". exact Logic.I. Qed.
Print Assumptions refine_Periodic_correspondence.
Goal Logic.True. idtac "AUDIT_END refine_Periodic_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN refine_Sporadic_correspondence". exact Logic.I. Qed.
Print Assumptions refine_Sporadic_correspondence.
Goal Logic.True. idtac "AUDIT_END refine_Sporadic_correspondence". exact Logic.I. Qed.
