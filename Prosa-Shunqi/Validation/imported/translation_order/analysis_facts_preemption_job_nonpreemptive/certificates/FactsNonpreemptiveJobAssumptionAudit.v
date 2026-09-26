From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence FactsNonpreemptiveJobCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN valid_fully_nonpreemptive_model_correspondence". exact Logic.I. Qed.
Print Assumptions valid_fully_nonpreemptive_model_correspondence.
Goal Logic.True. idtac "AUDIT_END valid_fully_nonpreemptive_model_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_max_nps_is_job_cost_correspondence". exact Logic.I. Qed.
Print Assumptions job_max_nps_is_job_cost_correspondence.
Goal Logic.True. idtac "AUDIT_END job_max_nps_is_job_cost_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_last_nps_is_job_cost_correspondence". exact Logic.I. Qed.
Print Assumptions job_last_nps_is_job_cost_correspondence.
Goal Logic.True. idtac "AUDIT_END job_last_nps_is_job_cost_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN no_preemptions_equiv_nonpreemptive_correspondence". exact Logic.I. Qed.
Print Assumptions no_preemptions_equiv_nonpreemptive_correspondence.
Goal Logic.True. idtac "AUDIT_END no_preemptions_equiv_nonpreemptive_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fnpj_forall_cover_sprop". exact Logic.I. Qed.
Print Assumptions fnpj_forall_cover_sprop.
Goal Logic.True. idtac "AUDIT_END fnpj_forall_cover_sprop". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fnpj_lean_transport". exact Logic.I. Qed.
Print Assumptions fnpj_lean_transport.
Goal Logic.True. idtac "AUDIT_END fnpj_lean_transport". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fnpj_nat_input". exact Logic.I. Qed.
Print Assumptions fnpj_nat_input.
Goal Logic.True. idtac "AUDIT_END fnpj_nat_input". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fnpj_fully_nonpreemptive_related". exact Logic.I. Qed.
Print Assumptions fnpj_fully_nonpreemptive_related.
Goal Logic.True. idtac "AUDIT_END fnpj_fully_nonpreemptive_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fnpj_unit_service_related". exact Logic.I. Qed.
Print Assumptions fnpj_unit_service_related.
Goal Logic.True. idtac "AUDIT_END fnpj_unit_service_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fnpj_nonpreemptive_schedule_related". exact Logic.I. Qed.
Print Assumptions fnpj_nonpreemptive_schedule_related.
Goal Logic.True. idtac "AUDIT_END fnpj_nonpreemptive_schedule_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fnpj_completed_jobs_dont_execute_related". exact Logic.I. Qed.
Print Assumptions fnpj_completed_jobs_dont_execute_related.
Goal Logic.True. idtac "AUDIT_END fnpj_completed_jobs_dont_execute_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fnpj_schedule_fun_to_svc". exact Logic.I. Qed.
Print Assumptions fnpj_schedule_fun_to_svc.
Goal Logic.True. idtac "AUDIT_END fnpj_schedule_fun_to_svc". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fnpj_schedule_to_target_rel". exact Logic.I. Qed.
Print Assumptions fnpj_schedule_to_target_rel.
Goal Logic.True. idtac "AUDIT_END fnpj_schedule_to_target_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fnpj_schedule_to_source_rel". exact Logic.I. Qed.
Print Assumptions fnpj_schedule_to_source_rel.
Goal Logic.True. idtac "AUDIT_END fnpj_schedule_to_source_rel". exact Logic.I. Qed.
