From FoundationCertificates Require Import
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations JitterReadyCorrespondence.

Goal Logic.True. idtac "AUDIT_BEGIN JobJitter_source_total". exact Logic.I. Qed.
Print Assumptions JobJitter_source_total.
Goal Logic.True. idtac "AUDIT_END JobJitter_source_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN JobJitter_target_total". exact Logic.I. Qed.
Print Assumptions JobJitter_target_total.
Goal Logic.True. idtac "AUDIT_END JobJitter_target_total". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN JobJitter_source_roundtrip". exact Logic.I. Qed.
Print Assumptions JobJitter_source_roundtrip.
Goal Logic.True. idtac "AUDIT_END JobJitter_source_roundtrip". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN is_released_correspondence". exact Logic.I. Qed.
Print Assumptions is_released_correspondence.
Goal Logic.True. idtac "AUDIT_END is_released_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jitter_ready_field_correspondence". exact Logic.I. Qed.
Print Assumptions jitter_ready_field_correspondence.
Goal Logic.True. idtac "AUDIT_END jitter_ready_field_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jitter_ready_law_statement_correspondence". exact Logic.I. Qed.
Print Assumptions jitter_ready_law_statement_correspondence.
Goal Logic.True. idtac "AUDIT_END jitter_ready_law_statement_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jitter_completed_by_related". exact Logic.I. Qed.
Print Assumptions jitter_completed_by_related.
Goal Logic.True. idtac "AUDIT_END jitter_completed_by_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN jitter_pending_related". exact Logic.I. Qed.
Print Assumptions jitter_pending_related.
Goal Logic.True. idtac "AUDIT_END jitter_pending_related". exact Logic.I. Qed.
