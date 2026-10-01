From FoundationCertificates Require Import
  IdlArrivalsSeqBaseAdapter IdlArrivalsSeqOperations IdlArrivalsSeqCorrespondence IdlArrivalsCorrespondence IdlWorkloadCorrespondence IdlAbstractDefinitionsBaseAdapter IdlServiceBaseAdapter IdlServiceNatBoolOperations IdlAbstractDefinitionsArrivalOperations IdlAbstractDefinitionsClasses IdlAbstractDefinitionsNatBoolOperations IdlAbstractDefinitionsIntervalOperations IdlAbstractDefinitionsOperations IdlAbstractDefinitionsSums IdlAbstractDefinitionsLogical IdlServiceIntervalOperations IdlServiceScheduleOperations IdlAbstractDefinitionsPendingOperations IdlAbstractDefinitionsTaskOperations IdlAbstractDefinitionsBusyIntervalHelpers IdlAbstractRtaHelpers IdlJitterSvcBaseAdapter IdlJitterSvcNatBoolOperations IdlJitterSvcIntervalOperations IdlJitterSvcScheduleOperations IdlJitterSvcJobOperations IdlPreemptionParameterCorrespondence IdlTaskPreemptionParametersCorrespondence IdlIdealAbstractRtaHelpers IdlArrivalSequenceBaseAdapter IdlArrivalSequenceOperations IdlTaskScheduleCorrespondence IdlCurvesCorrespondence IdlRequestBoundFunctionCorrespondence IdlSequentialityCorrespondence IdlServiceOfJobsCorrespondence IdlSupplyScheduleBaseAdapter IdlSupplyScheduleFiniteOperations IdlSupplyScheduleOperations IdlSupplyBaseAdapter IdlSupplyNatBoolOperations IdlSupplyIntervalOperations IdlSupplyCorrespondence IdlIbfTaskHelpers IdlIbfSupplyTaskCorrespondence IdlIbfTaskFullHelpers IdlServiceInversionPredCorrespondence IdlInterferenceCorrespondence IdlPriorityInversionCorrespondence IdlPreemptionTimeCorrespondence IdlEdfAthepBoundCorrespondence IdlNatSubCorrespondence IdlPcoBaseAdapter IdlPcoStaticOrder IdlPcoDynamicOrder IdlPriorityCoercionCorrespondence IdlPriorityGelHelpers IdlPriorityElfHelpers IdlStateRel RtaIdealElfBoundedPiCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN priority_inversion_bound_correspondence". exact Logic.I. Qed.
Print Assumptions priority_inversion_bound_correspondence.
Goal Logic.True. idtac "AUDIT_END priority_inversion_bound_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN priority_inversion_is_bounded_correspondence". exact Logic.I. Qed.
Print Assumptions priority_inversion_is_bounded_correspondence.
Goal Logic.True. idtac "AUDIT_END priority_inversion_is_bounded_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN instantiated_busy_intervals_are_bounded_correspondence". exact Logic.I. Qed.
Print Assumptions instantiated_busy_intervals_are_bounded_correspondence.
Goal Logic.True. idtac "AUDIT_END instantiated_busy_intervals_are_bounded_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN total_hp_rbf_correspondence". exact Logic.I. Qed.
Print Assumptions total_hp_rbf_correspondence.
Goal Logic.True. idtac "AUDIT_END total_hp_rbf_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ep_task_intf_interval_correspondence". exact Logic.I. Qed.
Print Assumptions ep_task_intf_interval_correspondence.
Goal Logic.True. idtac "AUDIT_END ep_task_intf_interval_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bound_on_total_ep_workload_correspondence". exact Logic.I. Qed.
Print Assumptions bound_on_total_ep_workload_correspondence.
Goal Logic.True. idtac "AUDIT_END bound_on_total_ep_workload_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN task_IBF_correspondence". exact Logic.I. Qed.
Print Assumptions task_IBF_correspondence.
Goal Logic.True. idtac "AUDIT_END task_IBF_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_of_hp_jobs_from_other_ep_tasks_correspondence". exact Logic.I. Qed.
Print Assumptions service_of_hp_jobs_from_other_ep_tasks_correspondence.
Goal Logic.True. idtac "AUDIT_END service_of_hp_jobs_from_other_ep_tasks_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cumulative_intf_ep_task_service_equiv_correspondence". exact Logic.I. Qed.
Print Assumptions cumulative_intf_ep_task_service_equiv_correspondence.
Goal Logic.True. idtac "AUDIT_END cumulative_intf_ep_task_service_equiv_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_of_hp_jobs_from_other_hp_tasks_correspondence". exact Logic.I. Qed.
Print Assumptions service_of_hp_jobs_from_other_hp_tasks_correspondence.
Goal Logic.True. idtac "AUDIT_END service_of_hp_jobs_from_other_hp_tasks_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cumulative_intf_hp_task_service_equiv_correspondence". exact Logic.I. Qed.
Print Assumptions cumulative_intf_hp_task_service_equiv_correspondence.
Goal Logic.True. idtac "AUDIT_END cumulative_intf_hp_task_service_equiv_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN total_workload_shorten_range_correspondence". exact Logic.I. Qed.
Print Assumptions total_workload_shorten_range_correspondence.
Goal Logic.True. idtac "AUDIT_END total_workload_shorten_range_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bound_on_ep_workload_correspondence". exact Logic.I. Qed.
Print Assumptions bound_on_ep_workload_correspondence.
Goal Logic.True. idtac "AUDIT_END bound_on_ep_workload_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bound_on_hp_workload_correspondence". exact Logic.I. Qed.
Print Assumptions bound_on_hp_workload_correspondence.
Goal Logic.True. idtac "AUDIT_END bound_on_hp_workload_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN instantiated_task_interference_is_bounded_correspondence". exact Logic.I. Qed.
Print Assumptions instantiated_task_interference_is_bounded_correspondence.
Goal Logic.True. idtac "AUDIT_END instantiated_task_interference_is_bounded_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN task_rbf_changes_at_correspondence". exact Logic.I. Qed.
Print Assumptions task_rbf_changes_at_correspondence.
Goal Logic.True. idtac "AUDIT_END task_rbf_changes_at_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bound_on_total_ep_workload_changes_at_correspondence". exact Logic.I. Qed.
Print Assumptions bound_on_total_ep_workload_changes_at_correspondence.
Goal Logic.True. idtac "AUDIT_END bound_on_total_ep_workload_changes_at_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN priority_inversion_changes_at_correspondence". exact Logic.I. Qed.
Print Assumptions priority_inversion_changes_at_correspondence.
Goal Logic.True. idtac "AUDIT_END priority_inversion_changes_at_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN is_in_search_space_correspondence". exact Logic.I. Qed.
Print Assumptions is_in_search_space_correspondence.
Goal Logic.True. idtac "AUDIT_END is_in_search_space_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN A_is_in_concrete_search_space_correspondence". exact Logic.I. Qed.
Print Assumptions A_is_in_concrete_search_space_correspondence.
Goal Logic.True. idtac "AUDIT_END A_is_in_concrete_search_space_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN response_time_recurrence_solution_exists_correspondence". exact Logic.I. Qed.
Print Assumptions response_time_recurrence_solution_exists_correspondence.
Goal Logic.True. idtac "AUDIT_END response_time_recurrence_solution_exists_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN uniprocessor_response_time_bound_elf_correspondence". exact Logic.I. Qed.
Print Assumptions uniprocessor_response_time_bound_elf_correspondence.
Goal Logic.True. idtac "AUDIT_END uniprocessor_response_time_bound_elf_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN relf_all_jobs_from_taskset_rel". exact Logic.I. Qed.
Print Assumptions relf_all_jobs_from_taskset_rel.
Goal Logic.True. idtac "AUDIT_END relf_all_jobs_from_taskset_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN relf_valid_taskset_curve_rel". exact Logic.I. Qed.
Print Assumptions relf_valid_taskset_curve_rel.
Goal Logic.True. idtac "AUDIT_END relf_valid_taskset_curve_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN relf_forall_fun". exact Logic.I. Qed.
Print Assumptions relf_forall_fun.
Goal Logic.True. idtac "AUDIT_END relf_forall_fun". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN relf_basic_ready_at". exact Logic.I. Qed.
Print Assumptions relf_basic_ready_at.
Goal Logic.True. idtac "AUDIT_END relf_basic_ready_at". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN relf_backlogged_rel". exact Logic.I. Qed.
Print Assumptions relf_backlogged_rel.
Goal Logic.True. idtac "AUDIT_END relf_backlogged_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN relf_respects_jlfp_rel". exact Logic.I. Qed.
Print Assumptions relf_respects_jlfp_rel.
Goal Logic.True. idtac "AUDIT_END relf_respects_jlfp_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN relf_decide_not". exact Logic.I. Qed.
Print Assumptions relf_decide_not.
Goal Logic.True. idtac "AUDIT_END relf_decide_not". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN relf_nat_neqb_related". exact Logic.I. Qed.
Print Assumptions relf_nat_neqb_related.
Goal Logic.True. idtac "AUDIT_END relf_nat_neqb_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN relf_has_canonical". exact Logic.I. Qed.
Print Assumptions relf_has_canonical.
Goal Logic.True. idtac "AUDIT_END relf_has_canonical". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN relf_has_related". exact Logic.I. Qed.
Print Assumptions relf_has_related.
Goal Logic.True. idtac "AUDIT_END relf_has_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN relf_subz_pp_le". exact Logic.I. Qed.
Print Assumptions relf_subz_pp_le.
Goal Logic.True. idtac "AUDIT_END relf_subz_pp_le". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN relf_subz_pp_gt". exact Logic.I. Qed.
Print Assumptions relf_subz_pp_gt.
Goal Logic.True. idtac "AUDIT_END relf_subz_pp_gt". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN relf_subz_pn". exact Logic.I. Qed.
Print Assumptions relf_subz_pn.
Goal Logic.True. idtac "AUDIT_END relf_subz_pn". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN relf_subz_np". exact Logic.I. Qed.
Print Assumptions relf_subz_np.
Goal Logic.True. idtac "AUDIT_END relf_subz_np". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN relf_subz_nn_le". exact Logic.I. Qed.
Print Assumptions relf_subz_nn_le.
Goal Logic.True. idtac "AUDIT_END relf_subz_nn_le". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN relf_subz_nn_gt". exact Logic.I. Qed.
Print Assumptions relf_subz_nn_gt.
Goal Logic.True. idtac "AUDIT_END relf_subz_nn_gt". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN relf_absmax_p". exact Logic.I. Qed.
Print Assumptions relf_absmax_p.
Goal Logic.True. idtac "AUDIT_END relf_absmax_p". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN relf_absmax_n". exact Logic.I. Qed.
Print Assumptions relf_absmax_n.
Goal Logic.True. idtac "AUDIT_END relf_absmax_n". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN relf_sub1_related". exact Logic.I. Qed.
Print Assumptions relf_sub1_related.
Goal Logic.True. idtac "AUDIT_END relf_sub1_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN relf_add1_related". exact Logic.I. Qed.
Print Assumptions relf_add1_related.
Goal Logic.True. idtac "AUDIT_END relf_add1_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN relf_sub_canonical". exact Logic.I. Qed.
Print Assumptions relf_sub_canonical.
Goal Logic.True. idtac "AUDIT_END relf_sub_canonical". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN relf_sub_related". exact Logic.I. Qed.
Print Assumptions relf_sub_related.
Goal Logic.True. idtac "AUDIT_END relf_sub_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN relf_absmax_canonical". exact Logic.I. Qed.
Print Assumptions relf_absmax_canonical.
Goal Logic.True. idtac "AUDIT_END relf_absmax_canonical". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN relf_absmax_related". exact Logic.I. Qed.
Print Assumptions relf_absmax_related.
Goal Logic.True. idtac "AUDIT_END relf_absmax_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN relf_int_neq_le". exact Logic.I. Qed.
Print Assumptions relf_int_neq_le.
Goal Logic.True. idtac "AUDIT_END relf_int_neq_le". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN relf_int_neq_related". exact Logic.I. Qed.
Print Assumptions relf_int_neq_related.
Goal Logic.True. idtac "AUDIT_END relf_int_neq_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN relf_cast_related". exact Logic.I. Qed.
Print Assumptions relf_cast_related.
Goal Logic.True. idtac "AUDIT_END relf_cast_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN relf_forall_fp". exact Logic.I. Qed.
Print Assumptions relf_forall_fp.
Goal Logic.True. idtac "AUDIT_END relf_forall_fp". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN relf_reflexive_task_priorities_rel". exact Logic.I. Qed.
Print Assumptions relf_reflexive_task_priorities_rel.
Goal Logic.True. idtac "AUDIT_END relf_reflexive_task_priorities_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN relf_fp_to_jlfp_rel". exact Logic.I. Qed.
Print Assumptions relf_fp_to_jlfp_rel.
Goal Logic.True. idtac "AUDIT_END relf_fp_to_jlfp_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN relf_addz_np". exact Logic.I. Qed.
Print Assumptions relf_addz_np.
Goal Logic.True. idtac "AUDIT_END relf_addz_np". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN relf_addz_nn". exact Logic.I. Qed.
Print Assumptions relf_addz_nn.
Goal Logic.True. idtac "AUDIT_END relf_addz_nn". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN relf_addz_canonical". exact Logic.I. Qed.
Print Assumptions relf_addz_canonical.
Goal Logic.True. idtac "AUDIT_END relf_addz_canonical". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN relf_addz_related". exact Logic.I. Qed.
Print Assumptions relf_addz_related.
Goal Logic.True. idtac "AUDIT_END relf_addz_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN relf_maxf_canonical". exact Logic.I. Qed.
Print Assumptions relf_maxf_canonical.
Goal Logic.True. idtac "AUDIT_END relf_maxf_canonical". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN relf_maxf_related". exact Logic.I. Qed.
Print Assumptions relf_maxf_related.
Goal Logic.True. idtac "AUDIT_END relf_maxf_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN relf_max_related". exact Logic.I. Qed.
Print Assumptions relf_max_related.
Goal Logic.True. idtac "AUDIT_END relf_max_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN relf_elf_rel". exact Logic.I. Qed.
Print Assumptions relf_elf_rel.
Goal Logic.True. idtac "AUDIT_END relf_elf_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN relf_task_pred_rel". exact Logic.I. Qed.
Print Assumptions relf_task_pred_rel.
Goal Logic.True. idtac "AUDIT_END relf_task_pred_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN relf_task_eq_rel". exact Logic.I. Qed.
Print Assumptions relf_task_eq_rel.
Goal Logic.True. idtac "AUDIT_END relf_task_eq_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN relf_transitive_rel". exact Logic.I. Qed.
Print Assumptions relf_transitive_rel.
Goal Logic.True. idtac "AUDIT_END relf_transitive_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN relf_total_rel". exact Logic.I. Qed.
Print Assumptions relf_total_rel.
Goal Logic.True. idtac "AUDIT_END relf_total_rel". exact Logic.I. Qed.
