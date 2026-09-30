From FoundationCertificates Require Import
  OvhArrivalsSeqBaseAdapter OvhArrivalsSeqOperations OvhArrivalsSeqCorrespondence OvhArrivalsCorrespondence OvhJitterSvcBaseAdapter OvhJitterSvcNatBoolOperations OvhJitterSvcIntervalOperations OvhJitterSvcScheduleOperations OvhJitterSvcJobOperations OvhPreemptionParameterCorrespondence OvhPreemptionTimeCorrespondence OvhPriorityDrivenCorrespondence OvhPStateCoverHelpers OvhFactsPreemptionHelpers OvhWorkloadCorrespondence OvhPriorityInversionCorrespondence OvhExistenceHelpers OvhHepAtPtHelpers OvhTaskPreemptionParametersCorrespondence OvhBusyIntervalPiHelpers OvhStateRel OvhCurvesCorrespondence ScheduleChangeBaseAdapter ScheduleChangeStateAdapter ScheduleChangeOptionOperations ScheduleChangeIntervalOperations ScheduleChangeListOperations ScheduleChangeCorrespondence OverheadsBaseAdapter OverheadsNatBoolOperations OverheadsIntervalOperations OverheadsCorrespondence OverheadResourceModelCorrespondence OsbfNatSub OsbfUnitGrowth OverheadsSbfJlfpCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN jlfp_blackout_bound_correspondence". exact Logic.I. Qed.
Print Assumptions jlfp_blackout_bound_correspondence.
Goal Logic.True. idtac "AUDIT_END jlfp_blackout_bound_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jlfp_ovh_sbf_slow_correspondence". exact Logic.I. Qed.
Print Assumptions jlfp_ovh_sbf_slow_correspondence.
Goal Logic.True. idtac "AUDIT_END jlfp_ovh_sbf_slow_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN overheads_sbf_monotone_correspondence". exact Logic.I. Qed.
Print Assumptions overheads_sbf_monotone_correspondence.
Goal Logic.True. idtac "AUDIT_END overheads_sbf_monotone_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jlfp_blackout_bound_monotone_correspondence". exact Logic.I. Qed.
Print Assumptions jlfp_blackout_bound_monotone_correspondence.
Goal Logic.True. idtac "AUDIT_END jlfp_blackout_bound_monotone_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN overheads_sbf_unit_correspondence". exact Logic.I. Qed.
Print Assumptions overheads_sbf_unit_correspondence.
Goal Logic.True. idtac "AUDIT_END overheads_sbf_unit_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN overheads_sbf_busy_valid_correspondence". exact Logic.I. Qed.
Print Assumptions overheads_sbf_busy_valid_correspondence.
Goal Logic.True. idtac "AUDIT_END overheads_sbf_busy_valid_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN osf_forall_list". exact Logic.I. Qed.
Print Assumptions osf_forall_list.
Goal Logic.True. idtac "AUDIT_END osf_forall_list". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN osf_andb_and". exact Logic.I. Qed.
Print Assumptions osf_andb_and.
Goal Logic.True. idtac "AUDIT_END osf_andb_and". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN osf_monotone_rel". exact Logic.I. Qed.
Print Assumptions osf_monotone_rel.
Goal Logic.True. idtac "AUDIT_END osf_monotone_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN osf_forall_ja". exact Logic.I. Qed.
Print Assumptions osf_forall_ja.
Goal Logic.True. idtac "AUDIT_END osf_forall_ja". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN osf_forall_cost". exact Logic.I. Qed.
Print Assumptions osf_forall_cost.
Goal Logic.True. idtac "AUDIT_END osf_forall_cost". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN osf_forall_jt". exact Logic.I. Qed.
Print Assumptions osf_forall_jt.
Goal Logic.True. idtac "AUDIT_END osf_forall_jt". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN osf_ovh_sched". exact Logic.I. Qed.
Print Assumptions osf_ovh_sched.
Goal Logic.True. idtac "AUDIT_END osf_ovh_sched". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN osf_basic_ready_rel". exact Logic.I. Qed.
Print Assumptions osf_basic_ready_rel.
Goal Logic.True. idtac "AUDIT_END osf_basic_ready_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN osf_preempted_at_related". exact Logic.I. Qed.
Print Assumptions osf_preempted_at_related.
Goal Logic.True. idtac "AUDIT_END osf_preempted_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN osf_no_superfluous_rel". exact Logic.I. Qed.
Print Assumptions osf_no_superfluous_rel.
Goal Logic.True. idtac "AUDIT_END osf_no_superfluous_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN osf_supply_at_related". exact Logic.I. Qed.
Print Assumptions osf_supply_at_related.
Goal Logic.True. idtac "AUDIT_END osf_supply_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN osf_supply_during_related". exact Logic.I. Qed.
Print Assumptions osf_supply_during_related.
Goal Logic.True. idtac "AUDIT_END osf_supply_during_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN osf_job_of_task_related". exact Logic.I. Qed.
Print Assumptions osf_job_of_task_related.
Goal Logic.True. idtac "AUDIT_END osf_job_of_task_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN osf_valid_busy_sbf_rel". exact Logic.I. Qed.
Print Assumptions osf_valid_busy_sbf_rel.
Goal Logic.True. idtac "AUDIT_END osf_valid_busy_sbf_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN osf_all_jobs_from_taskset_related". exact Logic.I. Qed.
Print Assumptions osf_all_jobs_from_taskset_related.
Goal Logic.True. idtac "AUDIT_END osf_all_jobs_from_taskset_related". exact Logic.I. Qed.
