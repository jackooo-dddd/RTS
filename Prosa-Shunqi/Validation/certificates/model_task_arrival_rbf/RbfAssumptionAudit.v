From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence RbfCorrespondence.

Goal Logic.True. idtac "AUDIT_BEGIN MaxRequestBound_source_total". exact Logic.I. Qed.
Print Assumptions MaxRequestBound_source_total.
Goal Logic.True. idtac "AUDIT_END MaxRequestBound_source_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN MaxRequestBound_target_total". exact Logic.I. Qed.
Print Assumptions MaxRequestBound_target_total.
Goal Logic.True. idtac "AUDIT_END MaxRequestBound_target_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN MinRequestBound_source_total". exact Logic.I. Qed.
Print Assumptions MinRequestBound_source_total.
Goal Logic.True. idtac "AUDIT_END MinRequestBound_source_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN MinRequestBound_target_total". exact Logic.I. Qed.
Print Assumptions MinRequestBound_target_total.
Goal Logic.True. idtac "AUDIT_END MinRequestBound_target_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN valid_request_bound_function_correspondence". exact Logic.I. Qed.
Print Assumptions valid_request_bound_function_correspondence.
Goal Logic.True. idtac "AUDIT_END valid_request_bound_function_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN respects_max_request_bound_correspondence". exact Logic.I. Qed.
Print Assumptions respects_max_request_bound_correspondence.
Goal Logic.True. idtac "AUDIT_END respects_max_request_bound_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN respects_min_request_bound_correspondence". exact Logic.I. Qed.
Print Assumptions respects_min_request_bound_correspondence.
Goal Logic.True. idtac "AUDIT_END respects_min_request_bound_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN valid_taskset_request_bound_function_correspondence". exact Logic.I. Qed.
Print Assumptions valid_taskset_request_bound_function_correspondence.
Goal Logic.True. idtac "AUDIT_END valid_taskset_request_bound_function_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN taskset_respects_max_request_bound_correspondence". exact Logic.I. Qed.
Print Assumptions taskset_respects_max_request_bound_correspondence.
Goal Logic.True. idtac "AUDIT_END taskset_respects_max_request_bound_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN taskset_respects_min_request_bound_correspondence". exact Logic.I. Qed.
Print Assumptions taskset_respects_min_request_bound_correspondence.
Goal Logic.True. idtac "AUDIT_END taskset_respects_min_request_bound_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rb_import_fun_rel". exact Logic.I. Qed.
Print Assumptions rb_import_fun_rel.
Goal Logic.True. idtac "AUDIT_END rb_import_fun_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rb_export_fun_rel". exact Logic.I. Qed.
Print Assumptions rb_export_fun_rel.
Goal Logic.True. idtac "AUDIT_END rb_export_fun_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rb_family_import". exact Logic.I. Qed.
Print Assumptions rb_family_import.
Goal Logic.True. idtac "AUDIT_END rb_family_import". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN rb_family_export". exact Logic.I. Qed.
Print Assumptions rb_family_export.
Goal Logic.True. idtac "AUDIT_END rb_family_export". exact Logic.I. Qed.
