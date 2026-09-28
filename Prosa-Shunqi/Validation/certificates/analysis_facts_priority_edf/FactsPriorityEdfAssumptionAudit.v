From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence PreemptionTimeCorrespondence PriorityDrivenCorrespondence PStateCoverHelpers FactsPreemptionHelpers FactsPriorityEdfCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN hep_job_deadline_correspondence". exact Logic.I. Qed.
Print Assumptions hep_job_deadline_correspondence.
Goal Logic.True. idtac "AUDIT_END hep_job_deadline_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN hep_job_task_deadline_correspondence". exact Logic.I. Qed.
Print Assumptions hep_job_task_deadline_correspondence.
Goal Logic.True. idtac "AUDIT_END hep_job_task_deadline_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN hep_job_arrival_edf_correspondence". exact Logic.I. Qed.
Print Assumptions hep_job_arrival_edf_correspondence.
Goal Logic.True. idtac "AUDIT_END hep_job_arrival_edf_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN EDF_respects_sequential_tasks_correspondence". exact Logic.I. Qed.
Print Assumptions EDF_respects_sequential_tasks_correspondence.
Goal Logic.True. idtac "AUDIT_END EDF_respects_sequential_tasks_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN EDF_implies_sequential_tasks_correspondence". exact Logic.I. Qed.
Print Assumptions EDF_implies_sequential_tasks_correspondence.
Goal Logic.True. idtac "AUDIT_END EDF_implies_sequential_tasks_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fpe_logic_eq_to_lean_eq". exact Logic.I. Qed.
Print Assumptions fpe_logic_eq_to_lean_eq.
Goal Logic.True. idtac "AUDIT_END fpe_logic_eq_to_lean_eq". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fpe_lean_transport". exact Logic.I. Qed.
Print Assumptions fpe_lean_transport.
Goal Logic.True. idtac "AUDIT_END fpe_lean_transport". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fpe_decide_eq_related". exact Logic.I. Qed.
Print Assumptions fpe_decide_eq_related.
Goal Logic.True. idtac "AUDIT_END fpe_decide_eq_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fpe_exists_identity". exact Logic.I. Qed.
Print Assumptions fpe_exists_identity.
Goal Logic.True. idtac "AUDIT_END fpe_exists_identity". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fpe_task_deadline_of_job_related". exact Logic.I. Qed.
Print Assumptions fpe_task_deadline_of_job_related.
Goal Logic.True. idtac "AUDIT_END fpe_task_deadline_of_job_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fpe_deadline_related". exact Logic.I. Qed.
Print Assumptions fpe_deadline_related.
Goal Logic.True. idtac "AUDIT_END fpe_deadline_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fpe_edf_rel". exact Logic.I. Qed.
Print Assumptions fpe_edf_rel.
Goal Logic.True. idtac "AUDIT_END fpe_edf_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fpe_same_task_related". exact Logic.I. Qed.
Print Assumptions fpe_same_task_related.
Goal Logic.True. idtac "AUDIT_END fpe_same_task_related". exact Logic.I. Qed.
