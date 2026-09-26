From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence WorkloadCorrespondence CurvesCorrespondence RequestBoundFunctionCorrespondence WorkloadBoundedCorrespondence DemandBoundFunctionCorrespondence FactsDbfCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN task_arrivals_with_deadline_within_eq_correspondence". exact Logic.I. Qed.
Print Assumptions task_arrivals_with_deadline_within_eq_correspondence.
Goal Logic.True. idtac "AUDIT_END task_arrivals_with_deadline_within_eq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN num_task_arrivals_with_deadline_within_eq_correspondence". exact Logic.I. Qed.
Print Assumptions num_task_arrivals_with_deadline_within_eq_correspondence.
Goal Logic.True. idtac "AUDIT_END num_task_arrivals_with_deadline_within_eq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN task_demand_within_correspondence". exact Logic.I. Qed.
Print Assumptions task_demand_within_correspondence.
Goal Logic.True. idtac "AUDIT_END task_demand_within_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN task_demand_within_le_task_dbf_correspondence". exact Logic.I. Qed.
Print Assumptions task_demand_within_le_task_dbf_correspondence.
Goal Logic.True. idtac "AUDIT_END task_demand_within_le_task_dbf_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN task_demand_within_le_task_rbf_shifted_correspondence". exact Logic.I. Qed.
Print Assumptions task_demand_within_le_task_rbf_shifted_correspondence.
Goal Logic.True. idtac "AUDIT_END task_demand_within_le_task_rbf_shifted_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN total_demand_within_correspondence". exact Logic.I. Qed.
Print Assumptions total_demand_within_correspondence.
Goal Logic.True. idtac "AUDIT_END total_demand_within_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN total_demand_within_le_total_dbf_correspondence". exact Logic.I. Qed.
Print Assumptions total_demand_within_le_total_dbf_correspondence.
Goal Logic.True. idtac "AUDIT_END total_demand_within_le_total_dbf_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN total_demand_within_le_sum_task_rbf_shifted_correspondence". exact Logic.I. Qed.
Print Assumptions total_demand_within_le_sum_task_rbf_shifted_correspondence.
Goal Logic.True. idtac "AUDIT_END total_demand_within_le_sum_task_rbf_shifted_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fdbf_forall_cover_sprop". exact Logic.I. Qed.
Print Assumptions fdbf_forall_cover_sprop.
Goal Logic.True. idtac "AUDIT_END fdbf_forall_cover_sprop". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fdbf_lean_transport". exact Logic.I. Qed.
Print Assumptions fdbf_lean_transport.
Goal Logic.True. idtac "AUDIT_END fdbf_lean_transport". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fdbf_list_eq_correspondence". exact Logic.I. Qed.
Print Assumptions fdbf_list_eq_correspondence.
Goal Logic.True. idtac "AUDIT_END fdbf_list_eq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fdbf_task_deadline_of_job_related". exact Logic.I. Qed.
Print Assumptions fdbf_task_deadline_of_job_related.
Goal Logic.True. idtac "AUDIT_END fdbf_task_deadline_of_job_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fdbf_job_deadline_related". exact Logic.I. Qed.
Print Assumptions fdbf_job_deadline_related.
Goal Logic.True. idtac "AUDIT_END fdbf_job_deadline_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fdbf_job_of_task_related". exact Logic.I. Qed.
Print Assumptions fdbf_job_of_task_related.
Goal Logic.True. idtac "AUDIT_END fdbf_job_of_task_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fdbf_task_cost_source_total". exact Logic.I. Qed.
Print Assumptions fdbf_task_cost_source_total.
Goal Logic.True. idtac "AUDIT_END fdbf_task_cost_source_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fdbf_task_cost_target_total". exact Logic.I. Qed.
Print Assumptions fdbf_task_cost_target_total.
Goal Logic.True. idtac "AUDIT_END fdbf_task_cost_target_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fdbf_job_cost_source_total". exact Logic.I. Qed.
Print Assumptions fdbf_job_cost_source_total.
Goal Logic.True. idtac "AUDIT_END fdbf_job_cost_source_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fdbf_job_cost_target_total". exact Logic.I. Qed.
Print Assumptions fdbf_job_cost_target_total.
Goal Logic.True. idtac "AUDIT_END fdbf_job_cost_target_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fdbf_list_to_target_rel". exact Logic.I. Qed.
Print Assumptions fdbf_list_to_target_rel.
Goal Logic.True. idtac "AUDIT_END fdbf_list_to_target_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fdbf_list_to_source_rel". exact Logic.I. Qed.
Print Assumptions fdbf_list_to_source_rel.
Goal Logic.True. idtac "AUDIT_END fdbf_list_to_source_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fdbf_valid_job_costs_related". exact Logic.I. Qed.
Print Assumptions fdbf_valid_job_costs_related.
Goal Logic.True. idtac "AUDIT_END fdbf_valid_job_costs_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fdbf_all_jobs_from_taskset_related". exact Logic.I. Qed.
Print Assumptions fdbf_all_jobs_from_taskset_related.
Goal Logic.True. idtac "AUDIT_END fdbf_all_jobs_from_taskset_related". exact Logic.I. Qed.
