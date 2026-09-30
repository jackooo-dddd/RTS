From FoundationCertificates Require Import
  IdlArrivalsSeqBaseAdapter IdlArrivalsSeqOperations IdlArrivalsSeqCorrespondence IdlArrivalsCorrespondence IdlWorkloadCorrespondence IdlAbstractDefinitionsBaseAdapter IdlServiceBaseAdapter IdlServiceNatBoolOperations IdlAbstractDefinitionsArrivalOperations IdlAbstractDefinitionsClasses IdlAbstractDefinitionsNatBoolOperations IdlAbstractDefinitionsIntervalOperations IdlAbstractDefinitionsOperations IdlAbstractDefinitionsSums IdlAbstractDefinitionsLogical IdlServiceIntervalOperations IdlServiceScheduleOperations IdlAbstractDefinitionsPendingOperations IdlAbstractDefinitionsTaskOperations IdlAbstractDefinitionsBusyIntervalHelpers IdlAbstractRtaHelpers IdlJitterSvcBaseAdapter IdlJitterSvcNatBoolOperations IdlJitterSvcIntervalOperations IdlJitterSvcScheduleOperations IdlJitterSvcJobOperations IdlPreemptionParameterCorrespondence IdlTaskPreemptionParametersCorrespondence IdlIdealAbstractRtaHelpers IdlArrivalSequenceBaseAdapter IdlArrivalSequenceOperations IdlTaskScheduleCorrespondence IdlCurvesCorrespondence IdlRequestBoundFunctionCorrespondence IdlSequentialityCorrespondence IdlServiceOfJobsCorrespondence IdlSupplyScheduleBaseAdapter IdlSupplyScheduleFiniteOperations IdlSupplyScheduleOperations IdlSupplyBaseAdapter IdlSupplyNatBoolOperations IdlSupplyIntervalOperations IdlSupplyCorrespondence IdlIbfTaskHelpers IdlIbfSupplyTaskCorrespondence IdlIbfTaskFullHelpers IdlServiceInversionPredCorrespondence IdlInterferenceCorrespondence IdlPriorityInversionCorrespondence IdlStateRel RtaIdealFpBoundedPiCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN is_in_search_space_correspondence". exact Logic.I. Qed.
Print Assumptions is_in_search_space_correspondence.
Goal Logic.True. idtac "AUDIT_END is_in_search_space_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN instantiated_busy_intervals_are_bounded_correspondence". exact Logic.I. Qed.
Print Assumptions instantiated_busy_intervals_are_bounded_correspondence.
Goal Logic.True. idtac "AUDIT_END instantiated_busy_intervals_are_bounded_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN instantiated_task_interference_is_bounded_correspondence". exact Logic.I. Qed.
Print Assumptions instantiated_task_interference_is_bounded_correspondence.
Goal Logic.True. idtac "AUDIT_END instantiated_task_interference_is_bounded_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN A_is_in_concrete_search_space_correspondence". exact Logic.I. Qed.
Print Assumptions A_is_in_concrete_search_space_correspondence.
Goal Logic.True. idtac "AUDIT_END A_is_in_concrete_search_space_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN correct_search_space_correspondence". exact Logic.I. Qed.
Print Assumptions correct_search_space_correspondence.
Goal Logic.True. idtac "AUDIT_END correct_search_space_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN uniprocessor_response_time_bound_fp_correspondence". exact Logic.I. Qed.
Print Assumptions uniprocessor_response_time_bound_fp_correspondence.
Goal Logic.True. idtac "AUDIT_END uniprocessor_response_time_bound_fp_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rif_forall_fp". exact Logic.I. Qed.
Print Assumptions rif_forall_fp.
Goal Logic.True. idtac "AUDIT_END rif_forall_fp". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rif_reflexive_task_priorities_rel". exact Logic.I. Qed.
Print Assumptions rif_reflexive_task_priorities_rel.
Goal Logic.True. idtac "AUDIT_END rif_reflexive_task_priorities_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rif_fp_to_jlfp_rel". exact Logic.I. Qed.
Print Assumptions rif_fp_to_jlfp_rel.
Goal Logic.True. idtac "AUDIT_END rif_fp_to_jlfp_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rif_all_jobs_from_taskset_rel". exact Logic.I. Qed.
Print Assumptions rif_all_jobs_from_taskset_rel.
Goal Logic.True. idtac "AUDIT_END rif_all_jobs_from_taskset_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rif_valid_taskset_curve_rel". exact Logic.I. Qed.
Print Assumptions rif_valid_taskset_curve_rel.
Goal Logic.True. idtac "AUDIT_END rif_valid_taskset_curve_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rif_decide_not". exact Logic.I. Qed.
Print Assumptions rif_decide_not.
Goal Logic.True. idtac "AUDIT_END rif_decide_not". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rif_nat_neqb_related". exact Logic.I. Qed.
Print Assumptions rif_nat_neqb_related.
Goal Logic.True. idtac "AUDIT_END rif_nat_neqb_related". exact Logic.I. Qed.
