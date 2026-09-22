From FoundationCertificates Require Import ServiceCorrespondence.

Goal True. idtac "AUDIT_BEGIN scheduled_at". exact I. Qed.
Print Assumptions scheduled_at_correspondence.
Goal True. idtac "AUDIT_END scheduled_at". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN service_at". exact I. Qed.
Print Assumptions service_at_correspondence.
Goal True. idtac "AUDIT_END service_at". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN receives_service_at". exact I. Qed.
Print Assumptions receives_service_at_correspondence.
Goal True. idtac "AUDIT_END receives_service_at". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN service_during". exact I. Qed.
Print Assumptions service_during_correspondence.
Goal True. idtac "AUDIT_END service_during". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN service". exact I. Qed.
Print Assumptions service_correspondence.
Goal True. idtac "AUDIT_END service". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN completed_by". exact I. Qed.
Print Assumptions completed_by_correspondence.
Goal True. idtac "AUDIT_END completed_by". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN completes_at". exact I. Qed.
Print Assumptions completes_at_correspondence.
Goal True. idtac "AUDIT_END completes_at". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN job_response_time_bound". exact I. Qed.
Print Assumptions job_response_time_bound_correspondence.
Goal True. idtac "AUDIT_END job_response_time_bound". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN job_meets_deadline". exact I. Qed.
Print Assumptions job_meets_deadline_correspondence.
Goal True. idtac "AUDIT_END job_meets_deadline". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN pending". exact I. Qed.
Print Assumptions pending_correspondence.
Goal True. idtac "AUDIT_END pending". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN pending_earlier_and_at". exact I. Qed.
Print Assumptions pending_earlier_and_at_correspondence.
Goal True. idtac "AUDIT_END pending_earlier_and_at". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN remaining_cost". exact I. Qed.
Print Assumptions remaining_cost_correspondence.
Goal True. idtac "AUDIT_END remaining_cost". exact I. Qed.
