From FoundationCertificates Require Import ScheduleProcessorStateCorrespondence.

Goal True. idtac "AUDIT_BEGIN ProcessorState". exact I. Qed.
Print Assumptions processor_state_observational_correspondence.
Goal True. idtac "AUDIT_END ProcessorState". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN scheduled_in". exact I. Qed.
Print Assumptions scheduled_in_certificate.
Goal True. idtac "AUDIT_END scheduled_in". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN supply_in". exact I. Qed.
Print Assumptions supply_in_certificate.
Goal True. idtac "AUDIT_END supply_in". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN service_in". exact I. Qed.
Print Assumptions service_in_certificate.
Goal True. idtac "AUDIT_END service_in". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN schedule_import". exact I. Qed.
Print Assumptions schedule_import_certificate.
Goal True. idtac "AUDIT_END schedule_import". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN schedule_export". exact I. Qed.
Print Assumptions schedule_export_certificate.
Goal True. idtac "AUDIT_END schedule_export". exact I. Qed.
