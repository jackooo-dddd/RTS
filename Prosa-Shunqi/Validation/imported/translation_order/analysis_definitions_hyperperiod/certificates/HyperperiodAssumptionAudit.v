From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence TaskOffsetCorrespondence PeriodicCorrespondence NatSubCorrespondence LcmseqBaseAdapter LcmseqDivModAdapter LcmseqCorrespondence HyperperiodCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN hyperperiod_correspondence". exact Logic.I. Qed.
Print Assumptions hyperperiod_correspondence.
Goal Logic.True. idtac "AUDIT_END hyperperiod_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN hyperperiod_index_correspondence". exact Logic.I. Qed.
Print Assumptions hyperperiod_index_correspondence.
Goal Logic.True. idtac "AUDIT_END hyperperiod_index_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN starting_instant_of_hyperperiod_correspondence". exact Logic.I. Qed.
Print Assumptions starting_instant_of_hyperperiod_correspondence.
Goal Logic.True. idtac "AUDIT_END starting_instant_of_hyperperiod_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN starting_instant_of_corresponding_hyperperiod_correspondence". exact Logic.I. Qed.
Print Assumptions starting_instant_of_corresponding_hyperperiod_correspondence.
Goal Logic.True. idtac "AUDIT_END starting_instant_of_corresponding_hyperperiod_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jobs_in_hyperperiod_correspondence". exact Logic.I. Qed.
Print Assumptions jobs_in_hyperperiod_correspondence.
Goal Logic.True. idtac "AUDIT_END jobs_in_hyperperiod_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_index_in_hyperperiod_correspondence". exact Logic.I. Qed.
Print Assumptions job_index_in_hyperperiod_correspondence.
Goal Logic.True. idtac "AUDIT_END job_index_in_hyperperiod_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN corresponding_job_in_hyperperiod_correspondence". exact Logic.I. Qed.
Print Assumptions corresponding_job_in_hyperperiod_correspondence.
Goal Logic.True. idtac "AUDIT_END corresponding_job_in_hyperperiod_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN hyp_period_map_canonical". exact Logic.I. Qed.
Print Assumptions hyp_period_map_canonical.
Goal Logic.True. idtac "AUDIT_END hyp_period_map_canonical". exact Logic.I. Qed.
