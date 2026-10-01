From FoundationCertificates Require Import
  IdlArrivalsSeqBaseAdapter IdlArrivalsSeqOperations IdlArrivalsSeqCorrespondence IdlArrivalsCorrespondence IdlWorkloadCorrespondence IdlAbstractDefinitionsBaseAdapter IdlServiceBaseAdapter IdlServiceNatBoolOperations IdlAbstractDefinitionsArrivalOperations IdlAbstractDefinitionsClasses IdlAbstractDefinitionsNatBoolOperations IdlAbstractDefinitionsIntervalOperations IdlAbstractDefinitionsOperations IdlAbstractDefinitionsSums IdlAbstractDefinitionsLogical IdlServiceIntervalOperations IdlServiceScheduleOperations IdlAbstractDefinitionsPendingOperations IdlAbstractDefinitionsTaskOperations IdlAbstractDefinitionsBusyIntervalHelpers IdlAbstractRtaHelpers IdlJitterSvcBaseAdapter IdlJitterSvcNatBoolOperations IdlJitterSvcIntervalOperations IdlJitterSvcScheduleOperations IdlJitterSvcJobOperations IdlPreemptionParameterCorrespondence IdlTaskPreemptionParametersCorrespondence IdlIdealAbstractRtaHelpers IdlArrivalSequenceBaseAdapter IdlArrivalSequenceOperations IdlTaskScheduleCorrespondence IdlCurvesCorrespondence IdlRequestBoundFunctionCorrespondence IdlSequentialityCorrespondence IdlServiceOfJobsCorrespondence IdlSupplyScheduleBaseAdapter IdlSupplyScheduleFiniteOperations IdlSupplyScheduleOperations IdlSupplyBaseAdapter IdlSupplyNatBoolOperations IdlSupplyIntervalOperations IdlSupplyCorrespondence IdlIbfTaskHelpers IdlIbfSupplyTaskCorrespondence IdlIbfTaskFullHelpers IdlServiceInversionPredCorrespondence IdlInterferenceCorrespondence IdlPriorityInversionCorrespondence IdlPreemptionTimeCorrespondence IdlStateRel RtaIdealFifoBoundedNpsCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN abstractly_work_conserving_correspondence". exact Logic.I. Qed.
Print Assumptions abstractly_work_conserving_correspondence.
Goal Logic.True. idtac "AUDIT_END abstractly_work_conserving_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN busy_windows_are_bounded_correspondence". exact Logic.I. Qed.
Print Assumptions busy_windows_are_bounded_correspondence.
Goal Logic.True. idtac "AUDIT_END busy_windows_are_bounded_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN no_priority_inversion_correspondence". exact Logic.I. Qed.
Print Assumptions no_priority_inversion_correspondence.
Goal Logic.True. idtac "AUDIT_END no_priority_inversion_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN IBF_correct_correspondence". exact Logic.I. Qed.
Print Assumptions IBF_correct_correspondence.
Goal Logic.True. idtac "AUDIT_END IBF_correct_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN is_in_concrete_search_space_correspondence". exact Logic.I. Qed.
Print Assumptions is_in_concrete_search_space_correspondence.
Goal Logic.True. idtac "AUDIT_END is_in_concrete_search_space_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN search_space_refinement_correspondence". exact Logic.I. Qed.
Print Assumptions search_space_refinement_correspondence.
Goal Logic.True. idtac "AUDIT_END search_space_refinement_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN soln_abstract_response_time_recurrence_correspondence". exact Logic.I. Qed.
Print Assumptions soln_abstract_response_time_recurrence_correspondence.
Goal Logic.True. idtac "AUDIT_END soln_abstract_response_time_recurrence_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN uniprocessor_response_time_bound_FIFO_correspondence". exact Logic.I. Qed.
Print Assumptions uniprocessor_response_time_bound_FIFO_correspondence.
Goal Logic.True. idtac "AUDIT_END uniprocessor_response_time_bound_FIFO_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rff_all_jobs_from_taskset_rel". exact Logic.I. Qed.
Print Assumptions rff_all_jobs_from_taskset_rel.
Goal Logic.True. idtac "AUDIT_END rff_all_jobs_from_taskset_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rff_valid_taskset_curve_rel". exact Logic.I. Qed.
Print Assumptions rff_valid_taskset_curve_rel.
Goal Logic.True. idtac "AUDIT_END rff_valid_taskset_curve_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rff_basic_ready_at". exact Logic.I. Qed.
Print Assumptions rff_basic_ready_at.
Goal Logic.True. idtac "AUDIT_END rff_basic_ready_at". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rff_backlogged_rel". exact Logic.I. Qed.
Print Assumptions rff_backlogged_rel.
Goal Logic.True. idtac "AUDIT_END rff_backlogged_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rff_respects_jlfp_rel". exact Logic.I. Qed.
Print Assumptions rff_respects_jlfp_rel.
Goal Logic.True. idtac "AUDIT_END rff_respects_jlfp_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rff_decide_not". exact Logic.I. Qed.
Print Assumptions rff_decide_not.
Goal Logic.True. idtac "AUDIT_END rff_decide_not". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rff_nat_neqb_related". exact Logic.I. Qed.
Print Assumptions rff_nat_neqb_related.
Goal Logic.True. idtac "AUDIT_END rff_nat_neqb_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rff_has_canonical". exact Logic.I. Qed.
Print Assumptions rff_has_canonical.
Goal Logic.True. idtac "AUDIT_END rff_has_canonical". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rff_has_related". exact Logic.I. Qed.
Print Assumptions rff_has_related.
Goal Logic.True. idtac "AUDIT_END rff_has_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rff_fifo_rel". exact Logic.I. Qed.
Print Assumptions rff_fifo_rel.
Goal Logic.True. idtac "AUDIT_END rff_fifo_rel". exact Logic.I. Qed.
