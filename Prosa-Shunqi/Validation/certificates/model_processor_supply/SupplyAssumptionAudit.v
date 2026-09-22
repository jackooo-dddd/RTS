From FoundationCertificates Require Import SupplyCorrespondence.

Goal True. idtac "AUDIT_BEGIN supply_bool_to_nat". exact I. Qed.
Print Assumptions supply_bool_to_nat_related.
Goal True. idtac "AUDIT_END supply_bool_to_nat". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN supply_at". exact I. Qed.
Print Assumptions supply_at_correspondence.
Goal True. idtac "AUDIT_END supply_at". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN supply_during". exact I. Qed.
Print Assumptions supply_during_correspondence.
Goal True. idtac "AUDIT_END supply_during". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN has_supply". exact I. Qed.
Print Assumptions has_supply_correspondence.
Goal True. idtac "AUDIT_END has_supply". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN is_blackout". exact I. Qed.
Print Assumptions is_blackout_correspondence.
Goal True. idtac "AUDIT_END is_blackout". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN blackout_during". exact I. Qed.
Print Assumptions blackout_during_correspondence.
Goal True. idtac "AUDIT_END blackout_during". exact I. Qed.
