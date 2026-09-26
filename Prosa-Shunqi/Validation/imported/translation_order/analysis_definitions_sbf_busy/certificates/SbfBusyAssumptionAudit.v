From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence BusyIntervalClassicalHelpers ArrivalSequenceBaseAdapter ArrivalSequenceOperations ArrivalSequenceCorrespondence SupplyScheduleBaseAdapter SupplyScheduleFiniteOperations SupplyScheduleOperations SupplyBaseAdapter SupplyNatBoolOperations SupplyIntervalOperations SupplyCorrespondence PredHelpers SbfBusyCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN sbf_respected_in_busy_interval_correspondence". exact Logic.I. Qed.
Print Assumptions sbf_respected_in_busy_interval_correspondence.
Goal Logic.True. idtac "AUDIT_END sbf_respected_in_busy_interval_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN valid_busy_sbf_correspondence". exact Logic.I. Qed.
Print Assumptions valid_busy_sbf_correspondence.
Goal Logic.True. idtac "AUDIT_END valid_busy_sbf_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sbfb_task_eq_bool_related". exact Logic.I. Qed.
Print Assumptions sbfb_task_eq_bool_related.
Goal Logic.True. idtac "AUDIT_END sbfb_task_eq_bool_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sbfb_job_of_task_related". exact Logic.I. Qed.
Print Assumptions sbfb_job_of_task_related.
Goal Logic.True. idtac "AUDIT_END sbfb_job_of_task_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sbfb_pred_related". exact Logic.I. Qed.
Print Assumptions sbfb_pred_related.
Goal Logic.True. idtac "AUDIT_END sbfb_pred_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN sbfb_arrival_sequence_rel". exact Logic.I. Qed.
Print Assumptions sbfb_arrival_sequence_rel.
Goal Logic.True. idtac "AUDIT_END sbfb_arrival_sequence_rel". exact Logic.I. Qed.
