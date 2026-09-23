From ImplementationCertificates Require Import ExtrapolatedArrivalCurveFactsCorrespondence.
Set Printing All.

Goal True. idtac "AUDIT_BEGIN ltn_steps_is_transitive". exact I. Qed.
Print Assumptions facts_ltn_steps_is_transitive_certificate.
Goal True. idtac "AUDIT_END ltn_steps_is_transitive". exact I. Qed.
Goal True. idtac "AUDIT_BEGIN leq_steps_is_reflexive". exact I. Qed.
Print Assumptions facts_leq_steps_is_reflexive_certificate.
Goal True. idtac "AUDIT_END leq_steps_is_reflexive". exact I. Qed.
Goal True. idtac "AUDIT_BEGIN leq_steps_is_transitive". exact I. Qed.
Print Assumptions facts_leq_steps_is_transitive_certificate.
Goal True. idtac "AUDIT_END leq_steps_is_transitive". exact I. Qed.
Goal True. idtac "AUDIT_BEGIN value_at_monotone". exact I. Qed.
Print Assumptions facts_value_at_monotone_certificate.
Goal True. idtac "AUDIT_END value_at_monotone". exact I. Qed.
Goal True. idtac "AUDIT_BEGIN value_at_change_is_in_steps_of". exact I. Qed.
Print Assumptions facts_value_at_change_is_in_steps_of_certificate.
Goal True. idtac "AUDIT_END value_at_change_is_in_steps_of". exact I. Qed.
Goal True. idtac "AUDIT_BEGIN sorted_ltn_steps_imply_sorted_leq_steps_steps". exact I. Qed.
Print Assumptions facts_sorted_ltn_implies_sorted_leq_certificate.
Goal True. idtac "AUDIT_END sorted_ltn_steps_imply_sorted_leq_steps_steps". exact I. Qed.
Goal True. idtac "AUDIT_BEGIN step_at_0_is_00". exact I. Qed.
Print Assumptions facts_step_at_zero_certificate.
Goal True. idtac "AUDIT_END step_at_0_is_00". exact I. Qed.
Goal True. idtac "AUDIT_BEGIN step_at_agrees_with_steps_of". exact I. Qed.
Print Assumptions facts_step_at_agrees_with_steps_of_certificate.
Goal True. idtac "AUDIT_END step_at_agrees_with_steps_of". exact I. Qed.
Goal True. idtac "AUDIT_BEGIN extrapolated_arrival_curve_is_monotone". exact I. Qed.
Print Assumptions facts_extrapolated_arrival_curve_is_monotone_certificate.
Goal True. idtac "AUDIT_END extrapolated_arrival_curve_is_monotone". exact I. Qed.
Goal True. idtac "AUDIT_BEGIN extrapolated_arrival_curve_change". exact I. Qed.
Print Assumptions facts_extrapolated_arrival_curve_change_certificate.
Goal True. idtac "AUDIT_END extrapolated_arrival_curve_change". exact I. Qed.
