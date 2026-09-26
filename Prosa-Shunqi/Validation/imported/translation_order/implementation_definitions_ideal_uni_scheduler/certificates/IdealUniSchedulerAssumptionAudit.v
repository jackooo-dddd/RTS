From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence IdealUniSchedulerCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN prev_job_nonpreemptive_correspondence". exact Logic.I. Qed.
Print Assumptions prev_job_nonpreemptive_correspondence.
Goal Logic.True. idtac "AUDIT_END prev_job_nonpreemptive_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN allocation_at_correspondence". exact Logic.I. Qed.
Print Assumptions allocation_at_correspondence.
Goal Logic.True. idtac "AUDIT_END allocation_at_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN pmc_uni_schedule_correspondence". exact Logic.I. Qed.
Print Assumptions pmc_uni_schedule_correspondence.
Goal Logic.True. idtac "AUDIT_END pmc_uni_schedule_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN choose_highest_prio_job_correspondence". exact Logic.I. Qed.
Print Assumptions choose_highest_prio_job_correspondence.
Goal Logic.True. idtac "AUDIT_END choose_highest_prio_job_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN uni_schedule_correspondence". exact Logic.I. Qed.
Print Assumptions uni_schedule_correspondence.
Goal Logic.True. idtac "AUDIT_END uni_schedule_correspondence". exact Logic.I. Qed.
