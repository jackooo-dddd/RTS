From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence InfiniteJobsCorrespondence.

Goal Logic.True. idtac "AUDIT_BEGIN infinite_jobs_correspondence". exact Logic.I. Qed.
Print Assumptions infinite_jobs_correspondence.
Goal Logic.True. idtac "AUDIT_END infinite_jobs_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arrives_in_correspondence_certificate". exact Logic.I. Qed.
Print Assumptions arrives_in_correspondence_certificate.
Goal Logic.True. idtac "AUDIT_END arrives_in_correspondence_certificate". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN job_index_correspondence". exact Logic.I. Qed.
Print Assumptions job_index_correspondence.
Goal Logic.True. idtac "AUDIT_END job_index_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN inf_exists_identity_correspondence". exact Logic.I. Qed.
Print Assumptions inf_exists_identity_correspondence.
Goal Logic.True. idtac "AUDIT_END inf_exists_identity_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN inf_eq_identity_correspondence". exact Logic.I. Qed.
Print Assumptions inf_eq_identity_correspondence.
Goal Logic.True. idtac "AUDIT_END inf_eq_identity_correspondence". exact Logic.I. Qed.
