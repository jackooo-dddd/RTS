From ImplementationCertificates Require Import ExtrapolatedArrivalCurveBaseCorrespondence.
Set Printing All.

Goal True. idtac "AUDIT_BEGIN inter_arrival_to_prefix". exact I. Qed.
Print Assumptions eac_inter_arrival_to_prefix_correspondence.
Goal True. idtac "AUDIT_END inter_arrival_to_prefix". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN horizon_of". exact I. Qed.
Print Assumptions eac_horizon_of_correspondence.
Goal True. idtac "AUDIT_END horizon_of". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN steps_of". exact I. Qed.
Print Assumptions eac_steps_of_correspondence.
Goal True. idtac "AUDIT_END steps_of". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN time_steps_of". exact I. Qed.
Print Assumptions eac_time_steps_of_correspondence.
Goal True. idtac "AUDIT_END time_steps_of". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN step_at". exact I. Qed.
Print Assumptions eac_step_at_correspondence.
Goal True. idtac "AUDIT_END step_at". exact I. Qed.
Goal True. idtac "AUDIT_BEGIN value_at". exact I. Qed.
Print Assumptions eac_value_at_correspondence.
Goal True. idtac "AUDIT_END value_at". exact I. Qed.
