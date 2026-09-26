From FoundationCertificates Require Import
  ArrivalSequenceBaseAdapter ArrivalSequenceOperations ArrivalSequenceCorrespondence
  SupplyScheduleBaseAdapter SupplyScheduleFiniteOperations SupplyScheduleOperations
  SupplyBaseAdapter SupplyNatBoolOperations SupplyIntervalOperations SupplyCorrespondence
  PredCorrespondence PlainCorrespondence NatSubCorrespondence DivModCorrespondence
  AverageCorrespondence FactsSbfAverageCorrespondence.

Goal Logic.True. idtac "AUDIT_BEGIN arm_sbf_monotone_correspondence". exact Logic.I. Qed.
Print Assumptions arm_sbf_monotone_correspondence.
Goal Logic.True. idtac "AUDIT_END arm_sbf_monotone_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arm_sbf_unit_correspondence". exact Logic.I. Qed.
Print Assumptions arm_sbf_unit_correspondence.
Goal Logic.True. idtac "AUDIT_END arm_sbf_unit_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arm_sbf_valid_correspondence". exact Logic.I. Qed.
Print Assumptions arm_sbf_valid_correspondence.
Goal Logic.True. idtac "AUDIT_END arm_sbf_valid_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fsa_arm_sbf_related". exact Logic.I. Qed.
Print Assumptions fsa_arm_sbf_related.
Goal Logic.True. idtac "AUDIT_END fsa_arm_sbf_related". exact Logic.I. Qed.
