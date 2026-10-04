From FoundationCertificates Require Import ClassicTasksetRtaCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN TaskSetRTA_valid_jobs_with_jitter_correspondence". exact Logic.I. Qed.
Print Assumptions TaskSetRTA_valid_jobs_with_jitter_correspondence.
Goal Logic.True. idtac "AUDIT_END TaskSetRTA_valid_jobs_with_jitter_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN TaskSetRTA_valid_response_time_bound_of_tsk_i_correspondence". exact Logic.I. Qed.
Print Assumptions TaskSetRTA_valid_response_time_bound_of_tsk_i_correspondence.
Goal Logic.True. idtac "AUDIT_END TaskSetRTA_valid_response_time_bound_of_tsk_i_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cjr_forall_sched". exact Logic.I. Qed.
Print Assumptions cjr_forall_sched.
Goal Logic.True. idtac "AUDIT_END cjr_forall_sched". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cjr_forall_par". exact Logic.I. Qed.
Print Assumptions cjr_forall_par.
Goal Logic.True. idtac "AUDIT_END cjr_forall_par". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cjr_forall_arr". exact Logic.I. Qed.
Print Assumptions cjr_forall_arr.
Goal Logic.True. idtac "AUDIT_END cjr_forall_arr". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cjr_forall_rel". exact Logic.I. Qed.
Print Assumptions cjr_forall_rel.
Goal Logic.True. idtac "AUDIT_END cjr_forall_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cjr_forall_susp". exact Logic.I. Qed.
Print Assumptions cjr_forall_susp.
Goal Logic.True. idtac "AUDIT_END cjr_forall_susp". exact Logic.I. Qed.
