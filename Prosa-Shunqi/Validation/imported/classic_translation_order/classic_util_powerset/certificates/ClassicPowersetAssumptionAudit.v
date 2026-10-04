From FoundationCertificates Require Import ClassicPowersetCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN powerset_correspondence". exact Logic.I. Qed.
Print Assumptions powerset_correspondence.
Goal Logic.True. idtac "AUDIT_END powerset_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN mem_powerset_correspondence". exact Logic.I. Qed.
Print Assumptions mem_powerset_correspondence.
Goal Logic.True. idtac "AUDIT_END mem_powerset_correspondence". exact Logic.I. Qed.
