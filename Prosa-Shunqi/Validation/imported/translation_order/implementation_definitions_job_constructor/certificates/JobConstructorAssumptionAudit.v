From FoundationCertificates Require Import
  EacFullCorrespondence AbCorrespondence ImplTaskCorrespondence JobConstructorCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN Task_source_total". exact Logic.I. Qed.
Print Assumptions Task_source_total.
Goal Logic.True. idtac "AUDIT_END Task_source_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Task_target_total". exact Logic.I. Qed.
Print Assumptions Task_target_total.
Goal Logic.True. idtac "AUDIT_END Task_target_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Job_source_total". exact Logic.I. Qed.
Print Assumptions Job_source_total.
Goal Logic.True. idtac "AUDIT_END Job_source_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN Job_target_total". exact Logic.I. Qed.
Print Assumptions Job_target_total.
Goal Logic.True. idtac "AUDIT_END Job_target_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN generate_job_at_correspondence". exact Logic.I. Qed.
Print Assumptions generate_job_at_correspondence.
Goal Logic.True. idtac "AUDIT_END generate_job_at_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN generate_jobs_at_correspondence". exact Logic.I. Qed.
Print Assumptions generate_jobs_at_correspondence.
Goal Logic.True. idtac "AUDIT_END generate_jobs_at_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jc_jobs_export". exact Logic.I. Qed.
Print Assumptions jc_jobs_export.
Goal Logic.True. idtac "AUDIT_END jc_jobs_export". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jc_jobs_import". exact Logic.I. Qed.
Print Assumptions jc_jobs_import.
Goal Logic.True. idtac "AUDIT_END jc_jobs_import". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jc_jobs_source_roundtrip". exact Logic.I. Qed.
Print Assumptions jc_jobs_source_roundtrip.
Goal Logic.True. idtac "AUDIT_END jc_jobs_source_roundtrip". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jc_jobs_target_roundtrip". exact Logic.I. Qed.
Print Assumptions jc_jobs_target_roundtrip.
Goal Logic.True. idtac "AUDIT_END jc_jobs_target_roundtrip". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jc_range_succ". exact Logic.I. Qed.
Print Assumptions jc_range_succ.
Goal Logic.True. idtac "AUDIT_END jc_range_succ". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jc_generate_map_range". exact Logic.I. Qed.
Print Assumptions jc_generate_map_range.
Goal Logic.True. idtac "AUDIT_END jc_generate_map_range". exact Logic.I. Qed.
