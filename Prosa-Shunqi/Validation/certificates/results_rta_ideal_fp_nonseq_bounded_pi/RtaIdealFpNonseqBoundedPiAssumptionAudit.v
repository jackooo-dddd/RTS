From FoundationCertificates Require Import
  IdlArrivalsSeqBaseAdapter IdlArrivalsSeqOperations IdlArrivalsSeqCorrespondence IdlArrivalsCorrespondence IdlWorkloadCorrespondence IdlAbstractDefinitionsBaseAdapter IdlServiceBaseAdapter IdlServiceNatBoolOperations IdlAbstractDefinitionsArrivalOperations IdlAbstractDefinitionsClasses IdlAbstractDefinitionsNatBoolOperations IdlAbstractDefinitionsIntervalOperations IdlAbstractDefinitionsOperations IdlAbstractDefinitionsSums IdlAbstractDefinitionsLogical IdlServiceIntervalOperations IdlServiceScheduleOperations IdlAbstractDefinitionsPendingOperations IdlAbstractDefinitionsTaskOperations IdlAbstractDefinitionsBusyIntervalHelpers IdlAbstractRtaHelpers IdlJitterSvcBaseAdapter IdlJitterSvcNatBoolOperations IdlJitterSvcIntervalOperations IdlJitterSvcScheduleOperations IdlJitterSvcJobOperations IdlPreemptionParameterCorrespondence IdlTaskPreemptionParametersCorrespondence IdlIdealAbstractRtaHelpers IdlArrivalSequenceBaseAdapter IdlArrivalSequenceOperations IdlTaskScheduleCorrespondence IdlCurvesCorrespondence IdlRequestBoundFunctionCorrespondence IdlSequentialityCorrespondence IdlServiceOfJobsCorrespondence IdlSupplyScheduleBaseAdapter IdlSupplyScheduleFiniteOperations IdlSupplyScheduleOperations IdlSupplyBaseAdapter IdlSupplyNatBoolOperations IdlSupplyIntervalOperations IdlSupplyCorrespondence IdlIbfTaskHelpers IdlIbfSupplyTaskCorrespondence IdlIbfTaskFullHelpers IdlServiceInversionPredCorrespondence IdlInterferenceCorrespondence IdlPriorityInversionCorrespondence IdlStateRel RtaIdealFpNonseqBoundedPiCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN instantiated_busy_intervals_are_bounded_correspondence". exact Logic.I. Qed.
Print Assumptions instantiated_busy_intervals_are_bounded_correspondence.
Goal Logic.True. idtac "AUDIT_END instantiated_busy_intervals_are_bounded_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN IBF_correspondence". exact Logic.I. Qed.
Print Assumptions IBF_correspondence.
Goal Logic.True. idtac "AUDIT_END IBF_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN self_intf_bound_case1_correspondence". exact Logic.I. Qed.
Print Assumptions self_intf_bound_case1_correspondence.
Goal Logic.True. idtac "AUDIT_END self_intf_bound_case1_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN self_intf_bound_case2_correspondence". exact Logic.I. Qed.
Print Assumptions self_intf_bound_case2_correspondence.
Goal Logic.True. idtac "AUDIT_END self_intf_bound_case2_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN self_intf_bound_correspondence". exact Logic.I. Qed.
Print Assumptions self_intf_bound_correspondence.
Goal Logic.True. idtac "AUDIT_END self_intf_bound_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN instantiated_task_interference_is_bounded_correspondence". exact Logic.I. Qed.
Print Assumptions instantiated_task_interference_is_bounded_correspondence.
Goal Logic.True. idtac "AUDIT_END instantiated_task_interference_is_bounded_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN is_in_concrete_search_space_correspondence". exact Logic.I. Qed.
Print Assumptions is_in_concrete_search_space_correspondence.
Goal Logic.True. idtac "AUDIT_END is_in_concrete_search_space_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN A_is_in_concrete_search_space_correspondence". exact Logic.I. Qed.
Print Assumptions A_is_in_concrete_search_space_correspondence.
Goal Logic.True. idtac "AUDIT_END A_is_in_concrete_search_space_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN correct_search_space_correspondence". exact Logic.I. Qed.
Print Assumptions correct_search_space_correspondence.
Goal Logic.True. idtac "AUDIT_END correct_search_space_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN uniprocessor_response_time_bound_fp_correspondence". exact Logic.I. Qed.
Print Assumptions uniprocessor_response_time_bound_fp_correspondence.
Goal Logic.True. idtac "AUDIT_END uniprocessor_response_time_bound_fp_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rnsq_forall_fp". exact Logic.I. Qed.
Print Assumptions rnsq_forall_fp.
Goal Logic.True. idtac "AUDIT_END rnsq_forall_fp". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rnsq_reflexive_task_priorities_rel". exact Logic.I. Qed.
Print Assumptions rnsq_reflexive_task_priorities_rel.
Goal Logic.True. idtac "AUDIT_END rnsq_reflexive_task_priorities_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rnsq_fp_to_jlfp_rel". exact Logic.I. Qed.
Print Assumptions rnsq_fp_to_jlfp_rel.
Goal Logic.True. idtac "AUDIT_END rnsq_fp_to_jlfp_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rnsq_all_jobs_from_taskset_rel". exact Logic.I. Qed.
Print Assumptions rnsq_all_jobs_from_taskset_rel.
Goal Logic.True. idtac "AUDIT_END rnsq_all_jobs_from_taskset_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rnsq_valid_taskset_curve_rel". exact Logic.I. Qed.
Print Assumptions rnsq_valid_taskset_curve_rel.
Goal Logic.True. idtac "AUDIT_END rnsq_valid_taskset_curve_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rnsq_decide_not". exact Logic.I. Qed.
Print Assumptions rnsq_decide_not.
Goal Logic.True. idtac "AUDIT_END rnsq_decide_not". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rnsq_nat_neqb_related". exact Logic.I. Qed.
Print Assumptions rnsq_nat_neqb_related.
Goal Logic.True. idtac "AUDIT_END rnsq_nat_neqb_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rnsq_jr_commute". exact Logic.I. Qed.
Print Assumptions rnsq_jr_commute.
Goal Logic.True. idtac "AUDIT_END rnsq_jr_commute". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rnsq_max_related". exact Logic.I. Qed.
Print Assumptions rnsq_max_related.
Goal Logic.True. idtac "AUDIT_END rnsq_max_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rnsq_self_workload_rel". exact Logic.I. Qed.
Print Assumptions rnsq_self_workload_rel.
Goal Logic.True. idtac "AUDIT_END rnsq_self_workload_rel". exact Logic.I. Qed.
