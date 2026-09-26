From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations IdealScheduleCorrespondence.

Goal Logic.True. idtac "AUDIT_BEGIN ideal_proc_model_is_a_uniprocessor_model_correspondence". exact Logic.I. Qed.
Print Assumptions ideal_proc_model_is_a_uniprocessor_model_correspondence.
Goal Logic.True. idtac "AUDIT_END ideal_proc_model_is_a_uniprocessor_model_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_in_service_on_correspondence". exact Logic.I. Qed.
Print Assumptions service_in_service_on_correspondence.
Goal Logic.True. idtac "AUDIT_END service_in_service_on_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_in_def_correspondence". exact Logic.I. Qed.
Print Assumptions service_in_def_correspondence.
Goal Logic.True. idtac "AUDIT_END service_in_def_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ideal_proc_model_ensures_ideal_progress_correspondence". exact Logic.I. Qed.
Print Assumptions ideal_proc_model_ensures_ideal_progress_correspondence.
Goal Logic.True. idtac "AUDIT_END ideal_proc_model_ensures_ideal_progress_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ideal_proc_model_provides_unit_service_correspondence". exact Logic.I. Qed.
Print Assumptions ideal_proc_model_provides_unit_service_correspondence.
Goal Logic.True. idtac "AUDIT_END ideal_proc_model_provides_unit_service_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ideal_proc_model_provides_unit_supply_correspondence". exact Logic.I. Qed.
Print Assumptions ideal_proc_model_provides_unit_supply_correspondence.
Goal Logic.True. idtac "AUDIT_END ideal_proc_model_provides_unit_supply_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN scheduled_in_def_correspondence". exact Logic.I. Qed.
Print Assumptions scheduled_in_def_correspondence.
Goal Logic.True. idtac "AUDIT_END scheduled_in_def_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN scheduled_at_def_correspondence". exact Logic.I. Qed.
Print Assumptions scheduled_at_def_correspondence.
Goal Logic.True. idtac "AUDIT_END scheduled_at_def_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_on_def_correspondence". exact Logic.I. Qed.
Print Assumptions service_on_def_correspondence.
Goal Logic.True. idtac "AUDIT_END service_on_def_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_at_def_correspondence". exact Logic.I. Qed.
Print Assumptions service_at_def_correspondence.
Goal Logic.True. idtac "AUDIT_END service_at_def_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_in_is_scheduled_in_correspondence". exact Logic.I. Qed.
Print Assumptions service_in_is_scheduled_in_correspondence.
Goal Logic.True. idtac "AUDIT_END service_in_is_scheduled_in_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_at_is_scheduled_at_correspondence". exact Logic.I. Qed.
Print Assumptions service_at_is_scheduled_at_correspondence.
Goal Logic.True. idtac "AUDIT_END service_at_is_scheduled_at_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ideal_proc_model_fully_consuming_correspondence". exact Logic.I. Qed.
Print Assumptions ideal_proc_model_fully_consuming_correspondence.
Goal Logic.True. idtac "AUDIT_END ideal_proc_model_fully_consuming_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ideal_proc_has_supply_correspondence". exact Logic.I. Qed.
Print Assumptions ideal_proc_has_supply_correspondence.
Goal Logic.True. idtac "AUDIT_END ideal_proc_has_supply_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ideal_proc_model_sched_case_analysis_correspondence". exact Logic.I. Qed.
Print Assumptions ideal_proc_model_sched_case_analysis_correspondence.
Goal Logic.True. idtac "AUDIT_END ideal_proc_model_sched_case_analysis_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ideal_sched_implies_not_idle_correspondence". exact Logic.I. Qed.
Print Assumptions ideal_sched_implies_not_idle_correspondence.
Goal Logic.True. idtac "AUDIT_END ideal_sched_implies_not_idle_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ideal_not_idle_implies_sched_correspondence". exact Logic.I. Qed.
Print Assumptions ideal_not_idle_implies_sched_correspondence.
Goal Logic.True. idtac "AUDIT_END ideal_not_idle_implies_sched_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN scheduled_job_at_def_correspondence". exact Logic.I. Qed.
Print Assumptions scheduled_job_at_def_correspondence.
Goal Logic.True. idtac "AUDIT_END scheduled_job_at_def_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN is_idle_def_correspondence". exact Logic.I. Qed.
Print Assumptions is_idle_def_correspondence.
Goal Logic.True. idtac "AUDIT_END is_idle_def_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_forall_cover_sprop". exact Logic.I. Qed.
Print Assumptions id_forall_cover_sprop.
Goal Logic.True. idtac "AUDIT_END id_forall_cover_sprop". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_lean_transport". exact Logic.I. Qed.
Print Assumptions id_lean_transport.
Goal Logic.True. idtac "AUDIT_END id_lean_transport". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_nat_input". exact Logic.I. Qed.
Print Assumptions id_nat_input.
Goal Logic.True. idtac "AUDIT_END id_nat_input". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_bool_eq_correspondence". exact Logic.I. Qed.
Print Assumptions id_bool_eq_correspondence.
Goal Logic.True. idtac "AUDIT_END id_bool_eq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_nat_eq_correspondence". exact Logic.I. Qed.
Print Assumptions id_nat_eq_correspondence.
Goal Logic.True. idtac "AUDIT_END id_nat_eq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_or_correspondence". exact Logic.I. Qed.
Print Assumptions id_or_correspondence.
Goal Logic.True. idtac "AUDIT_END id_or_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_not_correspondence". exact Logic.I. Qed.
Print Assumptions id_not_correspondence.
Goal Logic.True. idtac "AUDIT_END id_not_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_exists_identity_correspondence". exact Logic.I. Qed.
Print Assumptions id_exists_identity_correspondence.
Goal Logic.True. idtac "AUDIT_END id_exists_identity_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_eq_identity_correspondence". exact Logic.I. Qed.
Print Assumptions id_eq_identity_correspondence.
Goal Logic.True. idtac "AUDIT_END id_eq_identity_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_nat_of_bool_related". exact Logic.I. Qed.
Print Assumptions id_nat_of_bool_related.
Goal Logic.True. idtac "AUDIT_END id_nat_of_bool_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_opt_source_roundtrip". exact Logic.I. Qed.
Print Assumptions id_opt_source_roundtrip.
Goal Logic.True. idtac "AUDIT_END id_opt_source_roundtrip". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_opt_target_roundtrip". exact Logic.I. Qed.
Print Assumptions id_opt_target_roundtrip.
Goal Logic.True. idtac "AUDIT_END id_opt_target_roundtrip". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_opt_rel_canonical". exact Logic.I. Qed.
Print Assumptions id_opt_rel_canonical.
Goal Logic.True. idtac "AUDIT_END id_opt_rel_canonical". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_opt_rel_surjective". exact Logic.I. Qed.
Print Assumptions id_opt_rel_surjective.
Goal Logic.True. idtac "AUDIT_END id_opt_rel_surjective". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_opt_eq_correspondence". exact Logic.I. Qed.
Print Assumptions id_opt_eq_correspondence.
Goal Logic.True. idtac "AUDIT_END id_opt_eq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_option_some_eq_correspondence". exact Logic.I. Qed.
Print Assumptions id_option_some_eq_correspondence.
Goal Logic.True. idtac "AUDIT_END id_option_some_eq_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_option_none_eq_related". exact Logic.I. Qed.
Print Assumptions id_option_none_eq_related.
Goal Logic.True. idtac "AUDIT_END id_option_none_eq_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_src_scheduled_on". exact Logic.I. Qed.
Print Assumptions id_src_scheduled_on.
Goal Logic.True. idtac "AUDIT_END id_src_scheduled_on". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_src_scheduled_in". exact Logic.I. Qed.
Print Assumptions id_src_scheduled_in.
Goal Logic.True. idtac "AUDIT_END id_src_scheduled_in". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_src_service_in". exact Logic.I. Qed.
Print Assumptions id_src_service_in.
Goal Logic.True. idtac "AUDIT_END id_src_service_in". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_src_supply_in". exact Logic.I. Qed.
Print Assumptions id_src_supply_in.
Goal Logic.True. idtac "AUDIT_END id_src_supply_in". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_scheduled_in_related". exact Logic.I. Qed.
Print Assumptions id_scheduled_in_related.
Goal Logic.True. idtac "AUDIT_END id_scheduled_in_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_decide_state_related". exact Logic.I. Qed.
Print Assumptions id_decide_state_related.
Goal Logic.True. idtac "AUDIT_END id_decide_state_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_service_on_related". exact Logic.I. Qed.
Print Assumptions id_service_on_related.
Goal Logic.True. idtac "AUDIT_END id_service_on_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_service_in_related". exact Logic.I. Qed.
Print Assumptions id_service_in_related.
Goal Logic.True. idtac "AUDIT_END id_service_in_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_supply_in_related". exact Logic.I. Qed.
Print Assumptions id_supply_in_related.
Goal Logic.True. idtac "AUDIT_END id_supply_in_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_core_rel_surjective". exact Logic.I. Qed.
Print Assumptions id_core_rel_surjective.
Goal Logic.True. idtac "AUDIT_END id_core_rel_surjective". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_schedule_to_target_rel". exact Logic.I. Qed.
Print Assumptions id_schedule_to_target_rel.
Goal Logic.True. idtac "AUDIT_END id_schedule_to_target_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_schedule_to_source_rel". exact Logic.I. Qed.
Print Assumptions id_schedule_to_source_rel.
Goal Logic.True. idtac "AUDIT_END id_schedule_to_source_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_scheduled_at_related". exact Logic.I. Qed.
Print Assumptions id_scheduled_at_related.
Goal Logic.True. idtac "AUDIT_END id_scheduled_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_service_at_related". exact Logic.I. Qed.
Print Assumptions id_service_at_related.
Goal Logic.True. idtac "AUDIT_END id_service_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_supply_at_related". exact Logic.I. Qed.
Print Assumptions id_supply_at_related.
Goal Logic.True. idtac "AUDIT_END id_supply_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_ideal_is_idle_related". exact Logic.I. Qed.
Print Assumptions id_ideal_is_idle_related.
Goal Logic.True. idtac "AUDIT_END id_ideal_is_idle_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_scheduled_at_state_related". exact Logic.I. Qed.
Print Assumptions id_scheduled_at_state_related.
Goal Logic.True. idtac "AUDIT_END id_scheduled_at_state_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_scheduled_jobs_at_related". exact Logic.I. Qed.
Print Assumptions id_scheduled_jobs_at_related.
Goal Logic.True. idtac "AUDIT_END id_scheduled_jobs_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_scheduled_job_at_related". exact Logic.I. Qed.
Print Assumptions id_scheduled_job_at_related.
Goal Logic.True. idtac "AUDIT_END id_scheduled_job_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_is_idle_related". exact Logic.I. Qed.
Print Assumptions id_is_idle_related.
Goal Logic.True. idtac "AUDIT_END id_is_idle_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_jobs_come_from_related". exact Logic.I. Qed.
Print Assumptions id_jobs_come_from_related.
Goal Logic.True. idtac "AUDIT_END id_jobs_come_from_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_jobs_must_arrive_related". exact Logic.I. Qed.
Print Assumptions id_jobs_must_arrive_related.
Goal Logic.True. idtac "AUDIT_END id_jobs_must_arrive_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN id_arrival_sequence_to_source_rel". exact Logic.I. Qed.
Print Assumptions id_arrival_sequence_to_source_rel.
Goal Logic.True. idtac "AUDIT_END id_arrival_sequence_to_source_rel". exact Logic.I. Qed.
