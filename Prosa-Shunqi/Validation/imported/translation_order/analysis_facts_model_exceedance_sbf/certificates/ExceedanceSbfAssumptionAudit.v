From FoundationCertificates Require Import
  ExcArrivalsSeqBaseAdapter ExcArrivalsSeqOperations ExcArrivalsSeqCorrespondence ExcArrivalsCorrespondence ExcJitterSvcBaseAdapter ExcJitterSvcNatBoolOperations ExcJitterSvcIntervalOperations ExcJitterSvcScheduleOperations ExcJitterSvcJobOperations ExcPreemptionParameterCorrespondence ExcPreemptionTimeCorrespondence ExcPriorityDrivenCorrespondence ExcPStateCoverHelpers ExcFactsPreemptionHelpers ExcWorkloadCorrespondence ExcPriorityInversionCorrespondence ExcExistenceHelpers ExcHepAtPtHelpers ExcTaskPreemptionParametersCorrespondence ExcBusyIntervalPiHelpers ExcStateRel ExceedanceSbfCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN eps_sbf_correspondence". exact Logic.I. Qed.
Print Assumptions eps_sbf_correspondence.
Goal Logic.True. idtac "AUDIT_END eps_sbf_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN blackout_during_bounded_correspondence". exact Logic.I. Qed.
Print Assumptions blackout_during_bounded_correspondence.
Goal Logic.True. idtac "AUDIT_END blackout_during_bounded_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN eps_sbf_is_valid_correspondence". exact Logic.I. Qed.
Print Assumptions eps_sbf_is_valid_correspondence.
Goal Logic.True. idtac "AUDIT_END eps_sbf_is_valid_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN eps_sbf_is_unit_correspondence". exact Logic.I. Qed.
Print Assumptions eps_sbf_is_unit_correspondence.
Goal Logic.True. idtac "AUDIT_END eps_sbf_is_unit_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN esbf_andb_and". exact Logic.I. Qed.
Print Assumptions esbf_andb_and.
Goal Logic.True. idtac "AUDIT_END esbf_andb_and". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN esbf_eps_inst_related". exact Logic.I. Qed.
Print Assumptions esbf_eps_inst_related.
Goal Logic.True. idtac "AUDIT_END esbf_eps_inst_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN esbf_forall_ja". exact Logic.I. Qed.
Print Assumptions esbf_forall_ja.
Goal Logic.True. idtac "AUDIT_END esbf_forall_ja". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN esbf_forall_cost". exact Logic.I. Qed.
Print Assumptions esbf_forall_cost.
Goal Logic.True. idtac "AUDIT_END esbf_forall_cost". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN esbf_forall_jt". exact Logic.I. Qed.
Print Assumptions esbf_forall_jt.
Goal Logic.True. idtac "AUDIT_END esbf_forall_jt". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN esbf_is_exceedance_exec_related". exact Logic.I. Qed.
Print Assumptions esbf_is_exceedance_exec_related.
Goal Logic.True. idtac "AUDIT_END esbf_is_exceedance_exec_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN esbf_supply_at_related". exact Logic.I. Qed.
Print Assumptions esbf_supply_at_related.
Goal Logic.True. idtac "AUDIT_END esbf_supply_at_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN esbf_supply_during_related". exact Logic.I. Qed.
Print Assumptions esbf_supply_during_related.
Goal Logic.True. idtac "AUDIT_END esbf_supply_during_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN esbf_is_blackout_related". exact Logic.I. Qed.
Print Assumptions esbf_is_blackout_related.
Goal Logic.True. idtac "AUDIT_END esbf_is_blackout_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN esbf_blackout_related". exact Logic.I. Qed.
Print Assumptions esbf_blackout_related.
Goal Logic.True. idtac "AUDIT_END esbf_blackout_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN esbf_job_of_task_related". exact Logic.I. Qed.
Print Assumptions esbf_job_of_task_related.
Goal Logic.True. idtac "AUDIT_END esbf_job_of_task_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN esbf_valid_busy_sbf_rel". exact Logic.I. Qed.
Print Assumptions esbf_valid_busy_sbf_rel.
Goal Logic.True. idtac "AUDIT_END esbf_valid_busy_sbf_rel". exact Logic.I. Qed.
