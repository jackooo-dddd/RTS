From FoundationCertificates Require Import
  RacpBase RacpArrivalBound RacpTask RacpArrivalCurve RefArrivalCurvePrefixCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN has_valid_arrival_curve_prefix_tsk_correspondence". exact Logic.I. Qed.
Print Assumptions has_valid_arrival_curve_prefix_tsk_correspondence.
Goal Logic.True. idtac "AUDIT_END has_valid_arrival_curve_prefix_tsk_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN steps_are_positive_if_first_step_is_positive_correspondence". exact Logic.I. Qed.
Print Assumptions steps_are_positive_if_first_step_is_positive_correspondence.
Goal Logic.True. idtac "AUDIT_END steps_are_positive_if_first_step_is_positive_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN nonshifted_offsets_are_positive_correspondence". exact Logic.I. Qed.
Print Assumptions nonshifted_offsets_are_positive_correspondence.
Goal Logic.True. idtac "AUDIT_END nonshifted_offsets_are_positive_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN time_steps_sorted_correspondence". exact Logic.I. Qed.
Print Assumptions time_steps_sorted_correspondence.
Goal Logic.True. idtac "AUDIT_END time_steps_sorted_correspondence". exact Logic.I. Qed.
