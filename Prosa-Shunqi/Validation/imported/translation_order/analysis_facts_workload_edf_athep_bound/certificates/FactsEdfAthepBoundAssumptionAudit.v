From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence WorkloadCorrespondence CurvesCorrespondence RequestBoundFunctionCorrespondence WorkloadBoundedCorrespondence EdfAthepBoundCorrespondence FactsEdfAthepBoundCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN total_workload_shorten_range_correspondence". exact Logic.I. Qed.
Print Assumptions total_workload_shorten_range_correspondence.
Goal Logic.True. idtac "AUDIT_END total_workload_shorten_range_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sum_of_workloads_is_at_most_bound_on_total_hep_workload_correspondence". exact Logic.I. Qed.
Print Assumptions sum_of_workloads_is_at_most_bound_on_total_hep_workload_correspondence.
Goal Logic.True. idtac "AUDIT_END sum_of_workloads_is_at_most_bound_on_total_hep_workload_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bound_on_athep_workload_is_valid_correspondence". exact Logic.I. Qed.
Print Assumptions bound_on_athep_workload_is_valid_correspondence.
Goal Logic.True. idtac "AUDIT_END bound_on_athep_workload_is_valid_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN bound_on_athep_workload_monotone_correspondence". exact Logic.I. Qed.
Print Assumptions bound_on_athep_workload_monotone_correspondence.
Goal Logic.True. idtac "AUDIT_END bound_on_athep_workload_monotone_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN feab_forall_cover_sprop". exact Logic.I. Qed.
Print Assumptions feab_forall_cover_sprop.
Goal Logic.True. idtac "AUDIT_END feab_forall_cover_sprop". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN feab_lean_transport". exact Logic.I. Qed.
Print Assumptions feab_lean_transport.
Goal Logic.True. idtac "AUDIT_END feab_lean_transport". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN feab_nat_input". exact Logic.I. Qed.
Print Assumptions feab_nat_input.
Goal Logic.True. idtac "AUDIT_END feab_nat_input". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN feab_decide_eq_related". exact Logic.I. Qed.
Print Assumptions feab_decide_eq_related.
Goal Logic.True. idtac "AUDIT_END feab_decide_eq_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN feab_monotone_related". exact Logic.I. Qed.
Print Assumptions feab_monotone_related.
Goal Logic.True. idtac "AUDIT_END feab_monotone_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN feab_task_deadline_of_job_related". exact Logic.I. Qed.
Print Assumptions feab_task_deadline_of_job_related.
Goal Logic.True. idtac "AUDIT_END feab_task_deadline_of_job_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN feab_job_deadline_related". exact Logic.I. Qed.
Print Assumptions feab_job_deadline_related.
Goal Logic.True. idtac "AUDIT_END feab_job_deadline_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN feab_edf_related". exact Logic.I. Qed.
Print Assumptions feab_edf_related.
Goal Logic.True. idtac "AUDIT_END feab_edf_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN feab_job_task_eq_related". exact Logic.I. Qed.
Print Assumptions feab_job_task_eq_related.
Goal Logic.True. idtac "AUDIT_END feab_job_task_eq_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN feab_edf_from_related". exact Logic.I. Qed.
Print Assumptions feab_edf_from_related.
Goal Logic.True. idtac "AUDIT_END feab_edf_from_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN feab_job_of_task_related". exact Logic.I. Qed.
Print Assumptions feab_job_of_task_related.
Goal Logic.True. idtac "AUDIT_END feab_job_of_task_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN feab_job_cost_positive_related". exact Logic.I. Qed.
Print Assumptions feab_job_cost_positive_related.
Goal Logic.True. idtac "AUDIT_END feab_job_cost_positive_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN feab_task_cost_of_job_related". exact Logic.I. Qed.
Print Assumptions feab_task_cost_of_job_related.
Goal Logic.True. idtac "AUDIT_END feab_task_cost_of_job_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN feab_valid_job_costs_related". exact Logic.I. Qed.
Print Assumptions feab_valid_job_costs_related.
Goal Logic.True. idtac "AUDIT_END feab_valid_job_costs_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN feab_all_jobs_from_taskset_related". exact Logic.I. Qed.
Print Assumptions feab_all_jobs_from_taskset_related.
Goal Logic.True. idtac "AUDIT_END feab_all_jobs_from_taskset_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN feab_list_to_target_rel". exact Logic.I. Qed.
Print Assumptions feab_list_to_target_rel.
Goal Logic.True. idtac "AUDIT_END feab_list_to_target_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN feab_list_to_source_rel". exact Logic.I. Qed.
Print Assumptions feab_list_to_source_rel.
Goal Logic.True. idtac "AUDIT_END feab_list_to_source_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN feab_sched_to_target_rel". exact Logic.I. Qed.
Print Assumptions feab_sched_to_target_rel.
Goal Logic.True. idtac "AUDIT_END feab_sched_to_target_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN feab_sched_to_source_rel". exact Logic.I. Qed.
Print Assumptions feab_sched_to_source_rel.
Goal Logic.True. idtac "AUDIT_END feab_sched_to_source_rel". exact Logic.I. Qed.
