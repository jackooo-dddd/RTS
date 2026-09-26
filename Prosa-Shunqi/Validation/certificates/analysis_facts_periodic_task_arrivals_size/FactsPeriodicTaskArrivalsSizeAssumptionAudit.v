From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence TaskOffsetCorrespondence PeriodicCorrespondence InfiniteJobsCorrespondence FactsPeriodicTaskArrivalsSizeCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN task_arrivals_size_at_non_arrival_correspondence". exact Logic.I. Qed.
Print Assumptions task_arrivals_size_at_non_arrival_correspondence.
Goal Logic.True. idtac "AUDIT_END task_arrivals_size_at_non_arrival_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN task_arrivals_at_size_cases_correspondence". exact Logic.I. Qed.
Print Assumptions task_arrivals_at_size_cases_correspondence.
Goal Logic.True. idtac "AUDIT_END task_arrivals_at_size_cases_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN size_task_arrivals_between_eq0_correspondence". exact Logic.I. Qed.
Print Assumptions size_task_arrivals_between_eq0_correspondence.
Goal Logic.True. idtac "AUDIT_END size_task_arrivals_between_eq0_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jobs_exists_later_correspondence". exact Logic.I. Qed.
Print Assumptions jobs_exists_later_correspondence.
Goal Logic.True. idtac "AUDIT_END jobs_exists_later_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN task_arrivals_at_size_correspondence". exact Logic.I. Qed.
Print Assumptions task_arrivals_at_size_correspondence.
Goal Logic.True. idtac "AUDIT_END task_arrivals_at_size_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN size_task_arrivals_up_to_offset_correspondence". exact Logic.I. Qed.
Print Assumptions size_task_arrivals_up_to_offset_correspondence.
Goal Logic.True. idtac "AUDIT_END size_task_arrivals_up_to_offset_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN task_arrivals_up_to_size_correspondence". exact Logic.I. Qed.
Print Assumptions task_arrivals_up_to_size_correspondence.
Goal Logic.True. idtac "AUDIT_END task_arrivals_up_to_size_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN eq_size_of_task_arrivals_seperated_by_period_correspondence". exact Logic.I. Qed.
Print Assumptions eq_size_of_task_arrivals_seperated_by_period_correspondence.
Goal Logic.True. idtac "AUDIT_END eq_size_of_task_arrivals_seperated_by_period_correspondence". exact Logic.I. Qed.
