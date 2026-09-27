From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence WorkloadCorrespondence AbstractDefinitionsBaseAdapter ServiceBaseAdapter ServiceNatBoolOperations AbstractDefinitionsArrivalOperations AbstractDefinitionsClasses AbstractDefinitionsNatBoolOperations AbstractDefinitionsIntervalOperations AbstractDefinitionsOperations AbstractDefinitionsSums AbstractDefinitionsLogical ServiceIntervalOperations ServiceScheduleOperations AbstractDefinitionsPendingOperations AbstractDefinitionsTaskOperations AbstractDefinitionsBusyIntervalHelpers AbstractRtaHelpers SupplyScheduleBaseAdapter SupplyScheduleFiniteOperations SupplyScheduleOperations SupplyBaseAdapter SupplyNatBoolOperations SupplyIntervalOperations SupplyCorrespondence IbfSupplyCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence TaskPreemptionParametersCorrespondence PredCorrespondence BusySbfCorrespondence RsAbstractRtaCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN blackout_impl_interference_correspondence". exact Logic.I. Qed.
Print Assumptions blackout_impl_interference_correspondence.
Goal Logic.True. idtac "AUDIT_END blackout_impl_interference_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN blackout_plus_local_is_interference_correspondence". exact Logic.I. Qed.
Print Assumptions blackout_plus_local_is_interference_correspondence.
Goal Logic.True. idtac "AUDIT_END blackout_plus_local_is_interference_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN blackout_plus_local_is_interference_cumul_correspondence". exact Logic.I. Qed.
Print Assumptions blackout_plus_local_is_interference_cumul_correspondence.
Goal Logic.True. idtac "AUDIT_END blackout_plus_local_is_interference_cumul_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cumulative_job_interference_bound_correspondence". exact Logic.I. Qed.
Print Assumptions cumulative_job_interference_bound_correspondence.
Goal Logic.True. idtac "AUDIT_END cumulative_job_interference_bound_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN no_intra_interference_after_F_correspondence". exact Logic.I. Qed.
Print Assumptions no_intra_interference_after_F_correspondence.
Goal Logic.True. idtac "AUDIT_END no_intra_interference_after_F_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN IBF_P_bounds_interference_correspondence". exact Logic.I. Qed.
Print Assumptions IBF_P_bounds_interference_correspondence.
Goal Logic.True. idtac "AUDIT_END IBF_P_bounds_interference_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN IBF_NP_bounds_interference_correspondence". exact Logic.I. Qed.
Print Assumptions IBF_NP_bounds_interference_correspondence.
Goal Logic.True. idtac "AUDIT_END IBF_NP_bounds_interference_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN IBF_P_sol_le_IBF_NP_correspondence". exact Logic.I. Qed.
Print Assumptions IBF_P_sol_le_IBF_NP_correspondence.
Goal Logic.True. idtac "AUDIT_END IBF_P_sol_le_IBF_NP_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN max_in_rs_hypothesis_impl_max_in_arta_hypothesis_correspondence". exact Logic.I. Qed.
Print Assumptions max_in_rs_hypothesis_impl_max_in_arta_hypothesis_correspondence.
Goal Logic.True. idtac "AUDIT_END max_in_rs_hypothesis_impl_max_in_arta_hypothesis_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN uniprocessor_response_time_bound_restricted_supply_correspondence". exact Logic.I. Qed.
Print Assumptions uniprocessor_response_time_bound_restricted_supply_correspondence.
Goal Logic.True. idtac "AUDIT_END uniprocessor_response_time_bound_restricted_supply_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rs_hs_sup". exact Logic.I. Qed.
Print Assumptions rs_hs_sup.
Goal Logic.True. idtac "AUDIT_END rs_hs_sup". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rs_forall_sched". exact Logic.I. Qed.
Print Assumptions rs_forall_sched.
Goal Logic.True. idtac "AUDIT_END rs_forall_sched". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rs_forall_arr". exact Logic.I. Qed.
Print Assumptions rs_forall_arr.
Goal Logic.True. idtac "AUDIT_END rs_forall_arr". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rs_forall_state". exact Logic.I. Qed.
Print Assumptions rs_forall_state.
Goal Logic.True. idtac "AUDIT_END rs_forall_state". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rs_forall_sbf". exact Logic.I. Qed.
Print Assumptions rs_forall_sbf.
Goal Logic.True. idtac "AUDIT_END rs_forall_sbf". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rs_interference_related". exact Logic.I. Qed.
Print Assumptions rs_interference_related.
Goal Logic.True. idtac "AUDIT_END rs_interference_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rs_unit_supply_rel". exact Logic.I. Qed.
Print Assumptions rs_unit_supply_rel.
Goal Logic.True. idtac "AUDIT_END rs_unit_supply_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rs_scheduled_at_related". exact Logic.I. Qed.
Print Assumptions rs_scheduled_at_related.
Goal Logic.True. idtac "AUDIT_END rs_scheduled_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rs_must_arrive_rel". exact Logic.I. Qed.
Print Assumptions rs_must_arrive_rel.
Goal Logic.True. idtac "AUDIT_END rs_must_arrive_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rs_completed_dont_execute_rel". exact Logic.I. Qed.
Print Assumptions rs_completed_dont_execute_rel.
Goal Logic.True. idtac "AUDIT_END rs_completed_dont_execute_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rs_fully_consuming_rel". exact Logic.I. Qed.
Print Assumptions rs_fully_consuming_rel.
Goal Logic.True. idtac "AUDIT_END rs_fully_consuming_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rs_ibfp_rel". exact Logic.I. Qed.
Print Assumptions rs_ibfp_rel.
Goal Logic.True. idtac "AUDIT_END rs_ibfp_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rs_ibfnp_rel". exact Logic.I. Qed.
Print Assumptions rs_ibfnp_rel.
Goal Logic.True. idtac "AUDIT_END rs_ibfnp_rel". exact Logic.I. Qed.
