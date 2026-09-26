From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence PeriodicCorrespondence FactsPeriodicArrivalSeparationCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN consecutive_job_separation_correspondence". exact Logic.I. Qed.
Print Assumptions consecutive_job_separation_correspondence.
Goal Logic.True. idtac "AUDIT_END consecutive_job_separation_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_arrival_separation_when_index_diff_is_k_correspondence". exact Logic.I. Qed.
Print Assumptions job_arrival_separation_when_index_diff_is_k_correspondence.
Goal Logic.True. idtac "AUDIT_END job_arrival_separation_when_index_diff_is_k_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_sep_periodic_correspondence". exact Logic.I. Qed.
Print Assumptions job_sep_periodic_correspondence.
Goal Logic.True. idtac "AUDIT_END job_sep_periodic_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fpas_false_correspondence". exact Logic.I. Qed.
Print Assumptions fpas_false_correspondence.
Goal Logic.True. idtac "AUDIT_END fpas_false_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fpas_neq_correspondence". exact Logic.I. Qed.
Print Assumptions fpas_neq_correspondence.
Goal Logic.True. idtac "AUDIT_END fpas_neq_correspondence". exact Logic.I. Qed.
