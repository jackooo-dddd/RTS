From FoundationCertificates Require Import OverheadsCorrespondence.

Goal Logic.True. Proof. idtac "AUDIT_BEGIN proc_state". exact I. Qed.
Print Assumptions ovh_state_target_roundtrip.
Goal Logic.True. Proof. idtac "AUDIT_END proc_state". exact I. Qed.

Goal Logic.True. Proof. idtac "AUDIT_BEGIN overheads_scheduled_on". exact I. Qed.
Print Assumptions ovh_scheduled_on_correspondence.
Goal Logic.True. Proof. idtac "AUDIT_END overheads_scheduled_on". exact I. Qed.

Goal Logic.True. Proof. idtac "AUDIT_BEGIN overheads_supply_on". exact I. Qed.
Print Assumptions ovh_supply_on_correspondence.
Goal Logic.True. Proof. idtac "AUDIT_END overheads_supply_on". exact I. Qed.

Goal Logic.True. Proof. idtac "AUDIT_BEGIN overheads_service_on". exact I. Qed.
Print Assumptions ovh_service_on_correspondence.
Goal Logic.True. Proof. idtac "AUDIT_END overheads_service_on". exact I. Qed.

Goal Logic.True. Proof. idtac "AUDIT_BEGIN processor_state". exact I. Qed.
Print Assumptions ovh_processor_state_correspondence.
Goal Logic.True. Proof. idtac "AUDIT_END processor_state". exact I. Qed.

Goal Logic.True. Proof. idtac "AUDIT_BEGIN scheduled_job". exact I. Qed.
Print Assumptions ovh_scheduled_job_correspondence.
Goal Logic.True. Proof. idtac "AUDIT_END scheduled_job". exact I. Qed.

Goal Logic.True. Proof. idtac "AUDIT_BEGIN is_progress". exact I. Qed.
Print Assumptions ovh_is_progress_correspondence.
Goal Logic.True. Proof. idtac "AUDIT_END is_progress". exact I. Qed.

Goal Logic.True. Proof. idtac "AUDIT_BEGIN is_context_switch". exact I. Qed.
Print Assumptions ovh_is_context_switch_correspondence.
Goal Logic.True. Proof. idtac "AUDIT_END is_context_switch". exact I. Qed.

Goal Logic.True. Proof. idtac "AUDIT_BEGIN is_dispatch". exact I. Qed.
Print Assumptions ovh_is_dispatch_correspondence.
Goal Logic.True. Proof. idtac "AUDIT_END is_dispatch". exact I. Qed.

Goal Logic.True. Proof. idtac "AUDIT_BEGIN is_CRPD". exact I. Qed.
Print Assumptions ovh_is_CRPD_correspondence.
Goal Logic.True. Proof. idtac "AUDIT_END is_CRPD". exact I. Qed.

Goal Logic.True. Proof. idtac "AUDIT_BEGIN total_time_in_dispatch". exact I. Qed.
Print Assumptions ovh_total_time_in_dispatch_correspondence.
Goal Logic.True. Proof. idtac "AUDIT_END total_time_in_dispatch". exact I. Qed.

Goal Logic.True. Proof. idtac "AUDIT_BEGIN total_time_in_context_switch". exact I. Qed.
Print Assumptions ovh_total_time_in_context_switch_correspondence.
Goal Logic.True. Proof. idtac "AUDIT_END total_time_in_context_switch". exact I. Qed.

Goal Logic.True. Proof. idtac "AUDIT_BEGIN total_time_in_CRPD". exact I. Qed.
Print Assumptions ovh_total_time_in_CRPD_correspondence.
Goal Logic.True. Proof. idtac "AUDIT_END total_time_in_CRPD". exact I. Qed.
