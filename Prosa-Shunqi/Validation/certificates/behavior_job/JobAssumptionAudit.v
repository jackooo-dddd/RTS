From FoundationCertificates Require Import JobEqTypeAdapter JobCorrespondence.

Goal True. idtac "AUDIT_BEGIN JobType". exact I. Qed.
Print Assumptions job_type_equality_evidence_certificate.
Goal True. idtac "AUDIT_END JobType". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN work_total". exact I. Qed.
Print Assumptions work_relation_total_certificate.
Goal True. idtac "AUDIT_END work_total". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN work_source_roundtrip". exact I. Qed.
Print Assumptions work_source_roundtrip_certificate.
Goal True. idtac "AUDIT_END work_source_roundtrip". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN work_target_roundtrip". exact I. Qed.
Print Assumptions work_target_roundtrip_certificate.
Goal True. idtac "AUDIT_END work_target_roundtrip". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN JobCost_import". exact I. Qed.
Print Assumptions job_cost_import_certificate.
Goal True. idtac "AUDIT_END JobCost_import". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN JobCost_export". exact I. Qed.
Print Assumptions job_cost_export_certificate.
Goal True. idtac "AUDIT_END JobCost_export". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN JobCost_source_roundtrip". exact I. Qed.
Print Assumptions job_cost_source_roundtrip_certificate.
Goal True. idtac "AUDIT_END JobCost_source_roundtrip". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN JobCost_target_roundtrip". exact I. Qed.
Print Assumptions job_cost_target_roundtrip_certificate.
Goal True. idtac "AUDIT_END JobCost_target_roundtrip". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN JobArrival_import". exact I. Qed.
Print Assumptions job_arrival_import_certificate.
Goal True. idtac "AUDIT_END JobArrival_import". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN JobArrival_export". exact I. Qed.
Print Assumptions job_arrival_export_certificate.
Goal True. idtac "AUDIT_END JobArrival_export". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN JobArrival_source_roundtrip". exact I. Qed.
Print Assumptions job_arrival_source_roundtrip_certificate.
Goal True. idtac "AUDIT_END JobArrival_source_roundtrip". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN JobArrival_target_roundtrip". exact I. Qed.
Print Assumptions job_arrival_target_roundtrip_certificate.
Goal True. idtac "AUDIT_END JobArrival_target_roundtrip". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN JobDeadline_import". exact I. Qed.
Print Assumptions job_deadline_import_certificate.
Goal True. idtac "AUDIT_END JobDeadline_import". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN JobDeadline_export". exact I. Qed.
Print Assumptions job_deadline_export_certificate.
Goal True. idtac "AUDIT_END JobDeadline_export". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN JobDeadline_source_roundtrip". exact I. Qed.
Print Assumptions job_deadline_source_roundtrip_certificate.
Goal True. idtac "AUDIT_END JobDeadline_source_roundtrip". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN JobDeadline_target_roundtrip". exact I. Qed.
Print Assumptions job_deadline_target_roundtrip_certificate.
Goal True. idtac "AUDIT_END JobDeadline_target_roundtrip". exact I. Qed.
