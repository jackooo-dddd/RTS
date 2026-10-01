From FoundationCertificates Require Import
  IdlArrivalsSeqBaseAdapter IdlArrivalsSeqOperations IdlArrivalsSeqCorrespondence IdlArrivalsCorrespondence IdlWorkloadCorrespondence IdlAbstractDefinitionsBaseAdapter IdlServiceBaseAdapter IdlServiceNatBoolOperations IdlAbstractDefinitionsArrivalOperations IdlAbstractDefinitionsClasses IdlAbstractDefinitionsNatBoolOperations IdlAbstractDefinitionsIntervalOperations IdlAbstractDefinitionsOperations IdlAbstractDefinitionsSums IdlAbstractDefinitionsLogical IdlServiceIntervalOperations IdlServiceScheduleOperations IdlAbstractDefinitionsPendingOperations IdlAbstractDefinitionsTaskOperations IdlAbstractDefinitionsBusyIntervalHelpers IdlAbstractRtaHelpers IdlJitterSvcBaseAdapter IdlJitterSvcNatBoolOperations IdlJitterSvcIntervalOperations IdlJitterSvcScheduleOperations IdlJitterSvcJobOperations IdlPreemptionParameterCorrespondence IdlTaskPreemptionParametersCorrespondence IdlIdealAbstractRtaHelpers IdlArrivalSequenceBaseAdapter IdlArrivalSequenceOperations IdlTaskScheduleCorrespondence IdlCurvesCorrespondence IdlRequestBoundFunctionCorrespondence IdlSequentialityCorrespondence IdlServiceOfJobsCorrespondence IdlSupplyScheduleBaseAdapter IdlSupplyScheduleFiniteOperations IdlSupplyScheduleOperations IdlSupplyBaseAdapter IdlSupplyNatBoolOperations IdlSupplyIntervalOperations IdlSupplyCorrespondence IdlIbfTaskHelpers IdlIbfSupplyTaskCorrespondence IdlIbfTaskFullHelpers IdlServiceInversionPredCorrespondence IdlInterferenceCorrespondence IdlPriorityInversionCorrespondence IdlPreemptionTimeCorrespondence IdlEdfAthepBoundCorrespondence IdlStateRel RtaIdealEdfBoundedPiCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN task_rbf_changes_at_correspondence". exact Logic.I. Qed.
Print Assumptions task_rbf_changes_at_correspondence.
Goal Logic.True. idtac "AUDIT_END task_rbf_changes_at_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bound_on_total_hep_workload_changes_at_correspondence". exact Logic.I. Qed.
Print Assumptions bound_on_total_hep_workload_changes_at_correspondence.
Goal Logic.True. idtac "AUDIT_END bound_on_total_hep_workload_changes_at_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN priority_inversion_changes_at_correspondence". exact Logic.I. Qed.
Print Assumptions priority_inversion_changes_at_correspondence.
Goal Logic.True. idtac "AUDIT_END priority_inversion_changes_at_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN is_in_search_space_correspondence". exact Logic.I. Qed.
Print Assumptions is_in_search_space_correspondence.
Goal Logic.True. idtac "AUDIT_END is_in_search_space_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN instantiated_task_interference_is_bounded_correspondence". exact Logic.I. Qed.
Print Assumptions instantiated_task_interference_is_bounded_correspondence.
Goal Logic.True. idtac "AUDIT_END instantiated_task_interference_is_bounded_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN A_is_in_concrete_search_space_correspondence". exact Logic.I. Qed.
Print Assumptions A_is_in_concrete_search_space_correspondence.
Goal Logic.True. idtac "AUDIT_END A_is_in_concrete_search_space_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN correct_search_space_correspondence". exact Logic.I. Qed.
Print Assumptions correct_search_space_correspondence.
Goal Logic.True. idtac "AUDIT_END correct_search_space_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN uniprocessor_response_time_bound_edf_correspondence". exact Logic.I. Qed.
Print Assumptions uniprocessor_response_time_bound_edf_correspondence.
Goal Logic.True. idtac "AUDIT_END uniprocessor_response_time_bound_edf_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rie_all_jobs_from_taskset_rel". exact Logic.I. Qed.
Print Assumptions rie_all_jobs_from_taskset_rel.
Goal Logic.True. idtac "AUDIT_END rie_all_jobs_from_taskset_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rie_valid_taskset_curve_rel". exact Logic.I. Qed.
Print Assumptions rie_valid_taskset_curve_rel.
Goal Logic.True. idtac "AUDIT_END rie_valid_taskset_curve_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rie_forall_fun". exact Logic.I. Qed.
Print Assumptions rie_forall_fun.
Goal Logic.True. idtac "AUDIT_END rie_forall_fun". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rie_task_deadline_of_job_related". exact Logic.I. Qed.
Print Assumptions rie_task_deadline_of_job_related.
Goal Logic.True. idtac "AUDIT_END rie_task_deadline_of_job_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rie_edf_rel". exact Logic.I. Qed.
Print Assumptions rie_edf_rel.
Goal Logic.True. idtac "AUDIT_END rie_edf_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rie_basic_ready_at". exact Logic.I. Qed.
Print Assumptions rie_basic_ready_at.
Goal Logic.True. idtac "AUDIT_END rie_basic_ready_at". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rie_backlogged_rel". exact Logic.I. Qed.
Print Assumptions rie_backlogged_rel.
Goal Logic.True. idtac "AUDIT_END rie_backlogged_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rie_respects_jlfp_rel". exact Logic.I. Qed.
Print Assumptions rie_respects_jlfp_rel.
Goal Logic.True. idtac "AUDIT_END rie_respects_jlfp_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rie_decide_not". exact Logic.I. Qed.
Print Assumptions rie_decide_not.
Goal Logic.True. idtac "AUDIT_END rie_decide_not". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rie_nat_neqb_related". exact Logic.I. Qed.
Print Assumptions rie_nat_neqb_related.
Goal Logic.True. idtac "AUDIT_END rie_nat_neqb_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rie_has_canonical". exact Logic.I. Qed.
Print Assumptions rie_has_canonical.
Goal Logic.True. idtac "AUDIT_END rie_has_canonical". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rie_has_related". exact Logic.I. Qed.
Print Assumptions rie_has_related.
Goal Logic.True. idtac "AUDIT_END rie_has_related". exact Logic.I. Qed.
