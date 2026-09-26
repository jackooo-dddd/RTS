From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ServiceBaseAdapter ServiceNatBoolOperations ServiceIntervalOperations ServiceScheduleOperations AbstractDefinitionsBaseAdapter AbstractDefinitionsClasses AbstractDefinitionsSums AbstractDefinitionsBusyInterval PriorityBaseAdapter ReadinessInterferenceCorrespondence.

Goal Logic.True. idtac "AUDIT_BEGIN some_hep_job_ready_correspondence". exact Logic.I. Qed.
Print Assumptions some_hep_job_ready_correspondence.
Goal Logic.True. idtac "AUDIT_END some_hep_job_ready_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cumulative_readiness_interference_correspondence". exact Logic.I. Qed.
Print Assumptions cumulative_readiness_interference_correspondence.
Goal Logic.True. idtac "AUDIT_END cumulative_readiness_interference_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN readiness_interference_is_bounded_correspondence". exact Logic.I. Qed.
Print Assumptions readiness_interference_is_bounded_correspondence.
Goal Logic.True. idtac "AUDIT_END readiness_interference_is_bounded_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ri_has_related". exact Logic.I. Qed.
Print Assumptions ri_has_related.
Goal Logic.True. idtac "AUDIT_END ri_has_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN ad_busy_interval_prefix_correspondence". exact Logic.I. Qed.
Print Assumptions ad_busy_interval_prefix_correspondence.
Goal Logic.True. idtac "AUDIT_END ad_busy_interval_prefix_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN arrivals_up_to_correspondence_certificate". exact Logic.I. Qed.
Print Assumptions arrivals_up_to_correspondence_certificate.
Goal Logic.True. idtac "AUDIT_END arrivals_up_to_correspondence_certificate". exact Logic.I. Qed.
