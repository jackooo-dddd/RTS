From FoundationCertificates Require Import NonpreemptiveScheduleCorrespondence.

Goal Logic.True.
Proof. idtac "AUDIT_BEGIN nonpreemptive_schedule". exact I. Qed.
Print Assumptions nonpreemptive_schedule_correspondence.
Goal Logic.True.
Proof. idtac "AUDIT_END nonpreemptive_schedule". exact I. Qed.
