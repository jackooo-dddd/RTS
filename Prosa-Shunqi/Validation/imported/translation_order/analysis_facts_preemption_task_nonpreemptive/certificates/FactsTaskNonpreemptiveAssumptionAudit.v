From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence TaskPreemptionParametersCorrespondence TaskPreemptionFullyNonpreemptiveCorrespondence FactsTaskNonpreemptiveCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN fully_nonpreemptive_model_is_model_with_bounded_nonpreemptive_regions_correspondence". exact Logic.I. Qed.
Print Assumptions fully_nonpreemptive_model_is_model_with_bounded_nonpreemptive_regions_correspondence.
Goal Logic.True. idtac "AUDIT_END fully_nonpreemptive_model_is_model_with_bounded_nonpreemptive_regions_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fully_nonpreemptive_model_is_valid_model_with_bounded_nonpreemptive_regions_correspondence". exact Logic.I. Qed.
Print Assumptions fully_nonpreemptive_model_is_valid_model_with_bounded_nonpreemptive_regions_correspondence.
Goal Logic.True. idtac "AUDIT_END fully_nonpreemptive_model_is_valid_model_with_bounded_nonpreemptive_regions_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ftnp_lean_transport". exact Logic.I. Qed.
Print Assumptions ftnp_lean_transport.
Goal Logic.True. idtac "AUDIT_END ftnp_lean_transport". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ftnp_fully_nonpreemptive_job_related". exact Logic.I. Qed.
Print Assumptions ftnp_fully_nonpreemptive_job_related.
Goal Logic.True. idtac "AUDIT_END ftnp_fully_nonpreemptive_job_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ftnp_forall_cover_sprop". exact Logic.I. Qed.
Print Assumptions ftnp_forall_cover_sprop.
Goal Logic.True. idtac "AUDIT_END ftnp_forall_cover_sprop". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ftnp_nat_input". exact Logic.I. Qed.
Print Assumptions ftnp_nat_input.
Goal Logic.True. idtac "AUDIT_END ftnp_nat_input". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ftnp_task_cost_of_job_related". exact Logic.I. Qed.
Print Assumptions ftnp_task_cost_of_job_related.
Goal Logic.True. idtac "AUDIT_END ftnp_task_cost_of_job_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ftnp_valid_job_costs_related". exact Logic.I. Qed.
Print Assumptions ftnp_valid_job_costs_related.
Goal Logic.True. idtac "AUDIT_END ftnp_valid_job_costs_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ftnp_unit_service_related". exact Logic.I. Qed.
Print Assumptions ftnp_unit_service_related.
Goal Logic.True. idtac "AUDIT_END ftnp_unit_service_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ftnp_schedule_fun_to_svc". exact Logic.I. Qed.
Print Assumptions ftnp_schedule_fun_to_svc.
Goal Logic.True. idtac "AUDIT_END ftnp_schedule_fun_to_svc". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ftnp_schedule_to_target_rel". exact Logic.I. Qed.
Print Assumptions ftnp_schedule_to_target_rel.
Goal Logic.True. idtac "AUDIT_END ftnp_schedule_to_target_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ftnp_schedule_to_source_rel". exact Logic.I. Qed.
Print Assumptions ftnp_schedule_to_source_rel.
Goal Logic.True. idtac "AUDIT_END ftnp_schedule_to_source_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ftnp_nonpreemptive_schedule_related". exact Logic.I. Qed.
Print Assumptions ftnp_nonpreemptive_schedule_related.
Goal Logic.True. idtac "AUDIT_END ftnp_nonpreemptive_schedule_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ftnp_completed_jobs_dont_execute_related". exact Logic.I. Qed.
Print Assumptions ftnp_completed_jobs_dont_execute_related.
Goal Logic.True. idtac "AUDIT_END ftnp_completed_jobs_dont_execute_related". exact Logic.I. Qed.
